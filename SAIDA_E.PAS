UNIT Saida_e;
{
Rotina de saida e definicoes de precisao
V. 1.0 de 16/6/92
V. 1.0a de 03/06/93 Erro #1 explicado.
}

INTERFACE

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Crt;

{$IFDEF DOUBLE}
  TYPE REAL= {$IFDEF EXTENDED} EXTENDED {$ELSE} DOUBLE {$ENDIF};
{$ENDIF}

CONST
  precisao=
{$IFDEF DOUBLE}
  {$IFDEF EXTENDED} 'Extended' {$ELSE} 'Double' {$ENDIF}
{$ELSE} 'Single' {$ENDIF};
  procmodo={$IFDEF DPMI}'Protected'{$ELSE}'Real'{$ENDIF};

IMPLEMENTATION

VAR SaidaNormal:POINTER;

{$F+}
PROCEDURE MinhaSaida;
BEGIN
  ExitProc:=SaidaNormal;
  IF ExitCode<>0 THEN BEGIN
    {$IFNDEF DEBUG}
    TextMode(80);
    WriteLn;
    {$ENDIF}
    CASE ExitCode OF
        1:WriteLn('Graphics driver not found');
      203:WriteLn('Heap overflow');
      106:WriteLn('Invalid numerical format');
      200:WriteLn('Division by zero');
      202:WriteLn('Stack overflow');
      205:WriteLn('Overflow');
      207:WriteLn('Invalid numerical operation');
      255:WriteLn('Interrupted by user');
      ELSE WriteLn('Error # ',ExitCode);
    END;
    WriteLn
  END;
  {$IFNDEF DEBUG}
  ErrorAddr:=nil
  {$ENDIF}
END; {MinhaSaida}
{$F-}

BEGIN
  SaidaNormal:=ExitProc;
  ExitProc:=@MinhaSaida;
END.
