unit Zip;

interface

{$A-}

uses WinTypes, WinProcs, SysUtils, Classes, Math;

type
    EZipErr = class (Exception);

    SortType = (sRaw, sFullName, sFileName, sPathName, sCompressedSize,
                sOriginalSize, sCompressRatio, sDate);

    CompressType = (Stored, Shrunk, Reduce1, Reduce2, Reduce3, Reduce4,
                    Imploded, ResTokenised, Deflated, ResEnhancedDeflate,
                    ResPKLibrary);

    TZipFile = class (TObject)
    private
        Dir: TList;
        SortMap: TList;
        fd: Integer;
        fSort: SortType;
        pTail: Pointer;
        SelFiles: Integer;
        fName: String;
        fExtractDir: String;
        fPassword: String;
        fLowerCaseNames: Boolean;
        fReverseSort: Boolean;
        procedure LoadDirectory;
        procedure UnloadDirectory;
        function GetSigOffset (Signature: LongInt): LongInt;
        function GetDirectoryEntry (Idx: Integer): Pointer;
        function GetFilesCount: Integer;
        procedure SortFiles;
        procedure DoSort (L, R: Integer);
        function GetFullName (Index: Integer): String;
        function GetFileName (Index: Integer): String;
        function GetPathName (Index: Integer): String;
        function GetEncrypted (Index: Integer): Boolean;
        function GetCompressMethod (Index: Integer): CompressType;
        function GetCompressMethodName (Index: Integer): String;
        function GetCompressionRatio (Index: Integer): Integer;
        function GetDiskNumber (Index: Integer): Integer;
        function GetCrc32 (Index: Integer): LongInt;
        function GetCompressedSize (Index: Integer): LongInt;
        function GetOriginalSize (Index: Integer): LongInt;
        function GetDateTime (Index: Integer): TDateTime;
        function GetCommentLength (Index: Integer): Word;
        procedure SetZipName (const FileName: String);
        procedure SetSortType (Val: SortType);
        procedure SetReverseSort (Val: Boolean);
    public
        constructor Create (const FileName: String);
        destructor Destroy; override;
        procedure Reset;
        property FullName [Index: Integer]: String read GetFullName; default;
        property FileName [Index: Integer]: String read GetFileName;
        property PathName [Index: Integer]: String read GetPathName;
        property Encrypted [Index: Integer]: Boolean read GetEncrypted;
        property DiskNumber [Index: Integer]: Integer read GetDiskNumber;
        property Crc32 [Index: Integer]: LongInt read GetCrc32;
        property CompressMethod [Index: Integer]: CompressType read GetCompressMethod;
        property DateTime [Index: Integer]: TDateTime read GetDateTime;
        property CompressedSize [Index: Integer]: LongInt read GetCompressedSize;
        property OriginalSize [Index: Integer]: LongInt read GetOriginalSize;
        property CompressMethodName [Index: Integer]: String read GetCompressMethodName;
        property CommentLength [Index: Integer]: Word read GetCommentLength;
        property CompressionRatio [Index: Integer]: Integer read GetCompressionRatio;
    published
        property ZipName: String read fName write SetZipName;
        property SortStyle: SortType read fSort write SetSortType;
        property ExtractDir: String read fExtractDir write fExtractDir;
        property Password: String read fPassword write fPassword;
        property ReverseSort: Boolean read fReverseSort write SetReverseSort default False;
        property LowerCaseNames: Boolean read fLowerCaseNames write fLowerCaseNames default True;
        property FilesCount: Integer read GetFilesCount;
    end;

implementation

type
    PTailRec = ^TailRec;
    TailRec = record              { End of central dir - 'tail'        }
    Signature: LongInt;           { should be $06054b50                }
    ThisDisk: Word;               { # of this disk                     }
    DirDisk: Word;                { # of disk with central dir start   }
    NumEntries: Word;             { # of central dir entries this disk }
    TotEntries: Word;             { # of central dir entries total     }
    DirSize: LongInt;             { size of the central directory      }
    DirOffset: LongInt;           { offset of c-dir wrt starting disk  }
    BannerLength: Word;           { size of following comment (if any) }
end;

type
    PDirEntry = ^DirEntry;
    DirEntry = record             { Central Directory entry            }
    Signature: LongInt;           { should be $02014b50                }
    CreatorVersion: Word;         { version of ZIP that created it     }
    ExtractorVersion: Word;       { version of ZIP needed for extract  }
    GenBits: Word;                { general purpose bit flags          }
    CompressMethod: Word;         { compression method for this file   }
    DateTime: LongInt;            { file modification date/time        }
    crc32: LongInt;               { 32-bit file CRC                    }
    CompressedSize: LongInt;      { compressed size of file            }
    OriginalSize: LongInt;        { uncompressed size of file          }
    FileNameLen: Word;            { length of filename                 }
    ExtraLen: Word;               { length of extra info               }
    CommentLen: Word;             { length of comment stuff            }
    DiskNumStart: Word;           { starting disk number               }
    IFileAttribs: Word;           { File attributes                    }
    XFileAttribs: LongInt;        { External file attributes           }
    HeaderPos: LongInt;           { offset of local header             }
end;

function GetDirEntrySize (const Entry: DirEntry): Integer;
begin
    with Entry do Result := sizeof (DirEntry) + FileNameLen + ExtraLen + CommentLen;
end;

function IsValidTailPos (fd: Integer; tailPos: LongInt): Bool;
var
    tail: TailRec;
begin
    { This function is needed to cope with nested ZIP files  }
    { Without it, we might accidentally accept a tail marker }
    { inside a nested ZIP rather than the ZIP's own marker ! }

    Result := False;
    _llseek (fd, tailPos, 0);
    _lread (fd, @tail, sizeof (TailRec));
    if tail.Signature = $06054b50 then
    begin
        _llseek (fd, tail.DirOffset, 0);
        _lread (fd, @tail, sizeof (LongInt));
        Result := tail.Signature = $02014b50;
    end;
end;

function FindSig (fd: Integer; buff: PChar; len: Integer; fPos, Signature: LongInt): integer;
var
    p: PChar;
    pp: ^LongInt absolute p;
begin
    Result := -1;
    if len <> 0 then begin
        p := buff;
        while len <> 0 do begin
            if (pp^ = Signature) and IsValidTailPos (fd, fpos + p - buff) then begin
                Result := p - buff;
                Exit;
            end;

            Inc (p);
            Dec (len);
        end;
    end;
end;

{ These utility routines extract various fields from a DirEntry }

function DirGetFullName (pde: PDirEntry): String;
var
    Idx: Integer;
begin
    Result := '';
    if pde <> Nil then with pde^ do begin
        {$IFDEF WIN32} SetLength (Result, FileNameLen); {$ELSE} Result[0] := Chr(FileNameLen); {$ENDIF}
        Move ((PChar (pde) + sizeof (DirEntry))^, Result [1], FileNameLen);
        { Massage UNIX forward slashes to Wintel backslashes }
        for Idx := 1 to Length (Result) do
            if Result [Idx] = '/' then Result [Idx] := '\';
    end;
end;

function DirGetCompRatio (pde: PDirEntry): Double;
begin
    Result := 0;
    if pde <> Nil then with pde^ do
        if OriginalSize <> 0 then
            Result := ((OriginalSize - CompressedSize) * 100) / OriginalSize;
end;

{ TZipFile }

constructor TZipFile.Create (const FileName: String);
begin
    fd := -1;
    SortMap := TList.Create;
    fLowerCaseNames := True;
    fReverseSort := False;
    SetZipName (FileName);
end;

procedure TZipFile.SetZipName (const FileName: String);
var
    tail: TailRec;
    tailPos: LongInt;
    szName: array [0..255] of Char;
begin
    UnloadDirectory;
    fName := '';  fPassword := '';
    { If filename is empty, just exit }
    if FileName = '' then Exit;

    { Get the filename and make sure it has a proper extension }
    StrPCopy (szName, FileName);
    if StrPos (szName, '.') = Nil then lstrcat (szName, '.zip');

    { Now try to open the file }
    fd := _lopen (szName, of_Read or of_Share_Deny_Write);
    if fd = -1 then raise EZipErr.Create ('Cannot open specified file');
    fName := StrPas (szName);

    { OK - it's there, but is it a valid ZIP file ? }
    tailPos := GetSigOffset ($06054b50);
    if tailPos < 0 then raise EZipErr.Create ('Not a valid ZIP file');

    { Found the directory tail - ensure no disk spanning }
    _llseek (fd, tailPos, 0);
    _lread (fd, @tail, sizeof (TailRec));
    if (tail.ThisDisk <> 0) or (tail.DirDisk <> 0) then raise EZipErr.Create ('Disk spanning not yet implemented');

    { Read directory tail and banner into our data structure }
    GetMem (pTail, sizeof (TailRec) + tail.BannerLength);
    _llseek (fd, tailPos, 0);
    _lread (fd, PChar (pTail), sizeof (TailRec) + tail.BannerLength);

    { Now get the central directory & ensure all files selected }
    LoadDirectory;
end;

destructor TZipFile.Destroy;
begin
    UnloadDirectory;
    SortMap.Free;
    Inherited Destroy;
end;

procedure TZipFile.LoadDirectory;
var
    p: PChar;
    de: DirEntry;
    sz, Idx: Integer;

    function NonBlankEntry: Boolean;
    begin
        Result := (de.CompressedSize <> 0) or
                  (de.OriginalSize <> 0) or
                  (de.CompressMethod <> 0);
    end;

begin
    { Initialize directory TList }
    Dir := TList.Create;
    Dir.Capacity := PTailRec(pTail)^.NumEntries;
    { Seek to start of file }
    _llseek (fd, PTailRec(pTail)^.DirOffset, 0);
    { Read each entry in consecutively }
    for Idx := 0 to PTailRec(pTail)^.NumEntries - 1 do begin
        _lread (fd, @de, sizeof (de));
        sz := GetDirEntrySize (de);
        GetMem (p, sz);
        Move (de, p^, sizeof (de));
        _lread (fd, p + sizeof (de), sz - sizeof (de));

        { If this is a blank 'directory-marker' record, then skip it }
        if NonBlankEntry then Dir.Add (p) else FreeMem (p, sz);
    end;

    Reset;
end;

function TZipFile.GetDirectoryEntry (Idx: Integer): Pointer;
begin
    if Dir = Nil then raise EZipErr.Create ('No ZIP file specified');
    if fReverseSort then Idx := SortMap.Count - 1 - Idx;
    Result := SortMap [Idx];
end;

procedure TZipFile.DoSort (L, R: Integer);
var
    P: Pointer;
    I, J: Integer;

    function SortCompare (Key1, Key2: PDirEntry): Integer;
    var
        D1, D2: Double;
        S1, S2: String;
    begin
        D1 := 0; D2 := 0; Result := 0; { Just to shut the compiler up }
        case fSort of
            sFullName, sFileName, sPathName:
            begin
                S1 := DirGetFullName (Key1);
                S2 := DirGetFullName (Key2);
                if fSort = sFileName then begin
                    S1 := ExtractFileName (S1);
                    S2 := ExtractFileName (S2);
                end;
                if fSort = sPathName then begin
                    S1 := ExtractFilePath (S1);
                    S2 := ExtractFilePath (S2);
                end;
                Result := CompareText (S1, S2);
            end;

            sDate, sCompressedSize, sOriginalSize, sCompressRatio:
            begin
                if fSort = sDate then begin
                    D1 := FileDateToDateTime (Key1^.DateTime);
                    D2 := FileDateToDateTime (Key2^.DateTime);
                end;
                if fSort = sCompressedSize then begin
                    D1 := Key1^.CompressedSize;
                    D2 := Key2^.CompressedSize;
                end;
                if fSort = sOriginalSize then begin
                    D1 := Key1^.OriginalSize;
                    D2 := Key2^.OriginalSize;
                end;
                if fSort = sCompressRatio then begin
                    D1 := DirGetCompRatio (Key1);
                    D2 := DirGetCompRatio (Key2);
                end;

                if D1 = D2 then Result := 0 else if D1 > D2 then Result := 1 else Result := -1;
            end;
        end;
    end;

begin
    repeat
        I := L; J := R; P := SortMap [(L + R) shr 1];
        repeat
            while SortCompare (SortMap [I], P) < 0 do Inc(I);
            while SortCompare (SortMap [J], P) > 0 do Dec(J);
            if I <= J then begin SortMap.Exchange (I, J); Inc(I); Dec(J); end;
        until I > J;
        if L < J then DoSort (L, J);
        L := I;
    until I >= R;
end;

procedure TZipFile.SortFiles;
var
    Idx: Integer;
begin
    { First, clear the sort map }
    SortMap.Clear;
    SortMap.Capacity := FilesCount;
    { Initialise the sort map for 'sRaw' mode }
    for Idx := 0 to FilesCount - 1 do SortMap.Add (Dir [Idx]);
    { Now do the actual sort }
     if fSort <> sRaw then DoSort (0, SortMap.Count - 1);
end;

procedure TZipFile.SetSortType (Val: SortType);
begin
    fSort := Val;
    if Dir <> Nil then SortFiles;
end;

procedure TZipFile.SetReverseSort (Val: Boolean);
begin
    fReverseSort := Val;
end;

procedure TZipFile.Reset;
var
    idx: Integer;
begin
    SetSortType (fSort);
    SelFiles := FilesCount;
    for idx := 0 to SelFiles - 1 do
        PDirEntry (GetDirectoryEntry (idx))^.Signature := 1;
end;

procedure TZipFile.UnloadDirectory;

    procedure FreeList (var List: TList);
    var
        p: Pointer;
        Idx: Integer;
    begin
        if List <> Nil then
        begin
            for Idx := 0 to List.Count - 1 do
            begin
                p := List.Items [Idx];
                FreeMem (p, GetDirEntrySize (PDirEntry(p)^));
            end;

            List.Free;
            List := Nil;
        end;
    end;

begin
    FreeList (Dir);

    if pTail <> Nil then begin
        FreeMem (pTail, sizeof (TailRec) + PTailRec(pTail)^.BannerLength);
        pTail := Nil;
    end;

    if fd <> -1 then begin
        _lclose (fd);
        fd := -1;
    end;
end;

function TZipFile.GetSigOffset (Signature: LongInt): LongInt;
const
    InBufferSize = 8192;            { for sig searching }
var
    buff: PChar;
    fs, pos: LongInt;
    bp, bytesread: Integer;
begin
    GetMem (buff, InBufferSize);
    try
        fs := _llseek (fd, 0, 2);
        if fs <= InBuffersize then pos := 0 else pos := fs - InBufferSize;
        _llseek (fd, pos, 0);

        { Get initial buffer content }
        _lread (fd, buff, InBufferSize);
        bp := FindSig (fd, buff, InBufferSize, pos, Signature);

        { This is the main search loop... }
        while (bp < 0) and (pos > 0) do
        begin
            Move (buff, buff [InBufferSize - 4], 4);
            Dec (pos, InBufferSize - 4);
            if pos < 0 then pos := 0;
            _llseek (fd, pos, 0);
            bytesRead := _lread (fd, buff, InBufferSize - 4);
            if bytesRead < InBufferSize - 4 then Move (buff [InBufferSize - 4], buff [BytesRead], 4);
            if bytesRead > 0 then
            begin
                Inc (bytesRead, 4);
                bp := FindSig (fd, buff, bytesRead, pos, Signature);
            end;
        end;

        if bp < 0 then GetSigOffset := -1 else GetSigOffset := pos + bp;
    finally
        FreeMem (buff, InBufferSize);
    end;
end;

function TZipFile.GetFilesCount: Integer;
begin
    if Dir = Nil then raise EZipErr.Create ('No ZIP file specified');
    Result := Dir.Count;
end;

function TZipFile.GetFileName (Index: Integer): String;
begin
    Result := ExtractFileName (GetFullName (Index));
    if fLowerCaseNames then Result := LowerCase (Result);
end;

function TZipFile.GetPathName (Index: Integer): String;
begin
    Result := ExtractFilePath (GetFullName (Index));
end;

function TZipFile.GetFullName (Index: Integer): String;
begin
    Result := DirGetFullName (GetDirectoryEntry (Index));
end;

function TZipFile.GetDateTime (Index: Integer): TDateTime;
var
    pde: PDirEntry;
begin
    Result := 0;
    pde := GetDirectoryEntry (Index);
    if pde <> Nil then Result := FileDateToDateTime (pde^.DateTime);
end;

function TZipFile.GetEncrypted (Index: Integer): Boolean;
var
    pde: PDirEntry;
begin
    Result := False;
    pde := GetDirectoryEntry (Index);
    if pde <> Nil then Result := (pde^.GenBits and 1) <> 0;
end;

function TZipFile.GetCompressionRatio (Index: Integer): Integer;
begin
    Result := Round (DirGetCompRatio (GetDirectoryEntry (Index)));
end;

function TZipFile.GetCompressedSize (Index: Integer): LongInt;
var
    pde: PDirEntry;
begin
    Result := 0;
    pde := GetDirectoryEntry (Index);
    if pde <> Nil then Result := pde^.CompressedSize;
end;

function TZipFile.GetOriginalSize (Index: Integer): LongInt;
var
    pde: PDirEntry;
begin
    Result := 0;
    pde := GetDirectoryEntry (Index);
    if pde <> Nil then Result := pde^.OriginalSize;
end;

function TZipFile.GetCompressMethod (Index: Integer): CompressType;
var
    pde: PDirEntry;
begin
    Result := Stored;
    pde := GetDirectoryEntry (Index);
    if pde <> Nil then Result := CompressType (pde^.CompressMethod);
end;

function TZipFile.GetDiskNumber (Index: Integer): Integer;
var
    pde: PDirEntry;
begin
    Result := 1;
    pde := GetDirectoryEntry (Index);
    if pde <> Nil then Result := pde^.DiskNumStart;
end;

function TZipFile.GetCrc32 (Index: Integer): LongInt;
var
    pde: PDirEntry;
begin
    Result := 0;
    pde := GetDirectoryEntry (Index);
    if pde <> Nil then Result := pde^.crc32;
end;

function TZipFile.GetCommentLength (Index: Integer): Word;
var
    pde: PDirEntry;
begin
    Result := 0;
    pde := GetDirectoryEntry (Index);
    if pde <> Nil then Result := pde^.CommentLen;
end;

function TZipFile.GetCompressMethodName (Index: Integer): String;
var
    typ: CompressType;
begin
    typ := GetCompressMethod (Index);
    case typ of
        Stored:             Result := 'Stored';
        Shrunk:             Result := 'Shrunk';
        Reduce1..Reduce4:   Result := 'Reduced';
        Imploded:           Result := 'Imploded';
        Deflated:           Result := 'Deflated';
        else                Result := Format ('Unknown(%d)', [Ord (typ)]);
    end;
end;

end.

