UNIT GJ;
{
*****************************************************************************
Resolve um sistema de equacoes complexo com matrizes alocadas na "heap",
usando o metodo de Gauss-Jordan com condensacao pivotal.
Por: Antonio Carlos Moreirao de Queiroz - COPPE/DEEL/UFRJ 1993
V. 1.0 de 05/06/93
*****************************************************************************
}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

INTERFACE

{$IFDEF DOUBLE}
  TYPE REAL= {$IFDEF EXTENDED} EXTENDED {$ELSE} DOUBLE {$ENDIF};
{$ENDIF}

CONST
  MaxEqs=100;
  MaxFases=10;

TYPE
  rlinha=ARRAY[0..MaxEqs+MaxFases] OF REAL;
  ptrlinha=^rlinha;
  rcoluna=ARRAY[0..MaxEqs] OF ptrlinha;
  ptrmatriz=^rcoluna;
VAR
  Imag:REAL;
  Yr,Yi:ptrmatriz; {Sistema}
  {$IFDEF DETERMINANTE}
  dr,di:REAL;      {Determinante}
  {$ENDIF}
  dmin:REAL;       {Tolerancia para o determinante}
  sistema_alocado:BOOLEAN;

FUNCTION Cmult(x1,x2,y1,y2: REAL): REAL;
FUNCTION Cdiv(x1,x2,y1,y2: REAL): REAL;
FUNCTION AlocarSistema(eq,fases:INTEGER):BOOLEAN;
PROCEDURE DesalocarSistema;
FUNCTION ResolverSistema:BOOLEAN;

IMPLEMENTATION

VAR
  alinhas,acolunas:INTEGER;

FUNCTION Cmult(x1,x2,y1,y2: REAL): REAL;
BEGIN
  Cmult:=x1*y1-x2*y2;
  Imag:=x1*y2+x2*y1
END;

FUNCTION Cdiv(x1,x2,y1,y2: REAL): REAL;
VAR
  t:REAL;
BEGIN
  t:=y1*y1+y2*y2;
  Cdiv:=Cmult(x1,x2,y1,-y2)/t;
  Imag:=Imag/t
END;

FUNCTION AlocarMatriz(VAR p:ptrmatriz):BOOLEAN;
VAR
  i,j,tcoluna,tlinha:WORD;
BEGIN
  tcoluna:=(1+alinhas)*SizeOf(POINTER);
  tlinha:=(1+acolunas)*SizeOf(REAL);
  IF MaxAvail>tcoluna THEN BEGIN
    GetMem(p,tcoluna);
    FOR i:=0 TO alinhas DO
      IF MaxAvail>tlinha THEN
        GetMem(p^[i],tlinha)
      ELSE BEGIN
        FOR j:=i-1 DOWNTO 0 DO FreeMem(p^[j],tlinha);
        FreeMem(p,tcoluna);
        p:=nil;
        AlocarMatriz:=FALSE;
        Exit
      END;
    AlocarMatriz:=TRUE
  END
  ELSE AlocarMatriz:=FALSE
END;

PROCEDURE DesalocarMatriz(VAR p:ptrmatriz);
VAR
  i,tlinha:WORD;
BEGIN
  tlinha:=(1+acolunas)*SizeOf(REAL);
  FOR i:=alinhas DOWNTO 0 DO FreeMem(p^[i],tlinha);
  FreeMem(p,(1+alinhas)*SizeOf(POINTER));
  p:=nil;
END;

PROCEDURE DesalocarSistema;
BEGIN
  IF sistema_alocado THEN BEGIN
    DesalocarMatriz(Yr);
    DesalocarMatriz(Yi);
    sistema_alocado:=FALSE
  END;
END;

FUNCTION AlocarSistema(eq,fases:INTEGER):BOOLEAN;
BEGIN
  IF sistema_alocado THEN DesalocarSistema;
  alinhas:=eq; acolunas:=eq+fases;
  AlocarSistema:=AlocarMatriz(Yr) and AlocarMatriz(Yi);
  sistema_alocado:=TRUE
END;

FUNCTION ResolverSistema:BOOLEAN;
  VAR
    t,tr,ti,qr,qi:REAL;
    i,j,k,m:INTEGER;
    p:ptrlinha;
BEGIN
  {$IFDEF DETERMINANTE}
  dr:=1; di:=0;
  {$ENDIF}
  FOR i:=1 TO alinhas DO BEGIN
    tr:=0; ti:=0; m:=i;
    FOR k:=i TO alinhas DO
      IF Abs(Yr^[k]^[i])+Abs(Yi^[k]^[i])>Abs(tr)+Abs(ti) THEN BEGIN
        m:=k;
        tr:=Yr^[k]^[i];
        ti:=Yi^[k]^[i]
      END;
    IF i<>m THEN BEGIN
      {$IFDEF DETERMINANTE}
      dr:=-dr; di:=-di;
      {$ENDIF}
      p:=Yr^[i];
      Yr^[i]:=Yr^[m];
      Yr^[m]:=p;
      p:=Yi^[i];
      Yi^[i]:=Yi^[m];
      Yi^[m]:=p
    END;
    {$IFDEF DETERMINANTE}
    dr:=Cmult(tr,ti,dr,di); di:=Imag;
    {$ENDIF}
    t:=tr*tr+ti*ti;
    FOR j:=acolunas DOWNTO i+1 DO BEGIN
      IF t<=Sqr(dmin) THEN BEGIN
        ResolverSistema:=FALSE;
        Exit;
      END;
      qr:=(Yr^[i]^[j]*tr+Yi^[i]^[j]*ti)/t;
      qi:=(Yi^[i]^[j]*tr-Yr^[i]^[j]*ti)/t;
      Yi^[i]^[j]:=qi;
      Yr^[i]^[j]:=qr;
      FOR k:=1 TO alinhas DO
        IF i<>k THEN BEGIN
          Yr^[k]^[j]:=Yr^[k]^[j]-Cmult(Yr^[k]^[i],Yi^[k]^[i],qr,qi);
          Yi^[k]^[j]:=Yi^[k]^[j]-Imag
        END
    END
  END;
  FOR i:=alinhas+1 TO acolunas DO BEGIN
    Yr^[0]^[i]:=0;
    Yi^[0]^[i]:=0
  END;
  ResolverSistema:=TRUE
END; {ResolverSistema}

BEGIN
  dmin:=0;
  sistema_alocado:=FALSE
END.