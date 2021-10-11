unit Zipper;

interface

uses
  SysUtils, WinTypes, WinProcs, Messages, Classes, Graphics, Controls,
  Forms, Dialogs, StdCtrls, Menus, ExtCtrls, ZIP;

type
  TForm1 = class(TForm)
    MainMenu1: TMainMenu;
    File1: TMenuItem;
    Open1: TMenuItem;
    OpenDialog1: TOpenDialog;
    Panel1: TPanel;
    FileList: TListBox;
    Header1: THeader;
    NumFiles: TLabel;
    RevSort: TCheckBox;
    procedure Open1Click(Sender: TObject);
    procedure FileListDrawItem(Control: TWinControl; Index: Integer;
      Rect: TRect; State: TOwnerDrawState);
    procedure Header1Sized(Sender: TObject; ASection, AWidth: Integer);
    procedure FormResize(Sender: TObject);
    procedure FormCreate(Sender: TObject);
    procedure FormDestroy(Sender: TObject);
    procedure RevSortClick(Sender: TObject);
  private
    { Private declarations }
    zp: TZipFile;
    procedure FillList;
  public
    { Public declarations }
  end;

var
  Form1: TForm1;

implementation

{$R *.DFM}

procedure TForm1.FillList;
var
    p: String;
    idx: Integer;
begin
    FileList.Clear;
    FileList.Items.Capacity := zp.FilesCount;
    FileList.Items.BeginUpdate;
    
    for idx := 0 to zp.FilesCount - 1 do
    begin
        p := zp.FileName [idx] + '£' + FormatDateTime ('c', zp.DateTime [idx]);
        p := p + '£' + zp.CompressMethodName [Idx] + '£' + zp.PathName [Idx];
        fileList.Items.AddObject (p, TObject(idx));
    end;

    FileList.Items.EndUpdate;
    NumFiles.Caption := 'Files in archive = ' + IntToStr (zp.FilesCount);
end;

procedure TForm1.Open1Click(Sender: TObject);
begin
    if not OpenDialog1.Execute then Exit;
    zp.ZipName := OpenDialog1.FileName;
    FillList;
end;

function NextSection (var Str: String): String;
var
    idx: Integer;
begin
    if Str <> '' then idx := Pos ('£', Str) else idx := 0;
    if idx = 0 then
    begin
        NextSection := Str;
        Str := '';
    end
    else
    begin
        NextSection := Copy (Str, 1, idx - 1);
        Delete (Str, 1, idx);
    end;
end;

procedure TForm1.FileListDrawItem(Control: TWinControl; Index: Integer; Rect: TRect; State: TOwnerDrawState);
var
    Str: String;
    x, idx: Integer;
begin
    with FileList, FileList.Canvas, Header1 do
      begin
        idx := 0;
        FillRect (Rect);
        x := Rect.left + 3;
        Str := Items [Index];
        while Str<>'' do
          begin
            TextOut(x, Rect.top, NextSection (Str));
            Inc(x, SectionWidth [idx]);
            Inc(idx);
          end;
      end;
end;

procedure TForm1.Header1Sized(Sender: TObject; ASection, AWidth: Integer);
begin
    FileList.Invalidate;
end;

procedure TForm1.FormResize(Sender: TObject);
begin
    FileList.Width := Panel1.Width - 20;
    Header1.Width := FileList.Width;
end;

procedure TForm1.FormCreate(Sender: TObject);
begin
    zp := TZipFile.Create ('');
    zp.SortStyle := sFullName;
end;

procedure TForm1.FormDestroy(Sender: TObject);
begin
    zp.Free;
end;

procedure TForm1.RevSortClick(Sender: TObject);
begin
    zp.ReverseSort := RevSort.Checked;
    FillList;
end;

end.

