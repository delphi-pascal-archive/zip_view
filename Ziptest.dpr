program Ziptest;

uses
  Forms,
  Zipper in 'ZIPPER.PAS' {Form1},
  Zip in 'ZIP.PAS';

{$R *.RES}

begin
  Application.CreateForm(TForm1, Form1);
  Application.Run;
end.
