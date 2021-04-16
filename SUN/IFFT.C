/*
Versao Sun XView do programa IFFT
*******************************************************************************
Analise de Circuitos Lineares por Interpolacao por IFFT
Antonio Carlos Moreirao de Queiroz-COPPE/DEL-UFRJ-1995
V. 1.0 de 29/09/95 Traducao para C no IST,Lisboa. Completada em 8/11/95
*******************************************************************************
*/

#define versao "1.0 of 08/11/95"

#include <string.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <assert.h>
#include <time.h>
#include <floatingpoint.h>
#include <memory.h>

#include <X11/Xlib.h>
#include <xview/xview.h>
#include <xview/canvas.h>
#include <xview/xv_xrect.h>
#include <xview/cms.h>
#include <xview/textsw.h>
#include <xview/panel.h>
#include <xview/notice.h>
#include <xview/svrimage.h>
#include <xview/icon.h>

#define KTAB 9
#define KBS 8
#define KDEL 127
#define KCTRLB 2
#define KCTRLC 3
#define KCTRLK 11
#define KCTRLL 12
#define KCTRLO 15
#define KCTRLP 16
#define KCTRLQ 17
#define KCTRLR 18
#define KCTRLS 19
#define KCTRLT 20
#define KCTRLU 21
#define KCTRLV 22
#define KCTRLW 23
#define KCTRLY 25
#define KCTRLZ 26
#define KESC 27
#define KUPARROW 32596
#define KDOWNARROW 32602
#define KLEFTARROW 32598
#define KRIGHTARROW 32600
#define KPAGEUP 32597
#define KPAGEDOWN 32603
#define KF1 0
#define MAXCOR 6 
#define tamnome         5
#define MaxEl           170
#define MaxNos          40
#define MaxNos1         (MaxNos+1)
#define MaxNosAntes     50
#define Grmax           31
#define Gmax2           64 /* (Grmax*2) */
#define MeioGm          16 /* ((Grmax+1)/2) */
#define maxref          250
#define xxmax           199

#define xv_ok 1

#define RANDOM (double)random()/2147483647

/* Definicoes de tipos uteis e funcoes */
#define boolean unsigned char
#define true 1
#define false 0

/* defines para substituir xv_get e xv_set */

#define get_int(x) (int)xv_get(x,PANEL_VALUE)
#define get_real(x) atof((char*)xv_get(x,PANEL_VALUE))
#define get_text(x) (char*)xv_get(x,PANEL_VALUE)
#define get_dx(x) (int)xv_get(x,XV_WIDTH)
#define get_dy(x) (int)xv_get(x,XV_HEIGHT)
#define get_sel(x) (int)xv_get(x,PANEL_VALUE)
#define get_item(x) (int)xv_get(sel_menu,MENU_VALUE)-1
char buf[20];
#define set_int(x,y) xv_set(x,PANEL_VALUE,y,NULL)
#define set_real(x,y) xv_set(x,PANEL_VALUE,gcvt(y,15,buf),NULL)
#define set_sel(x,y) xv_set(x,PANEL_VALUE,y,NULL)
#define set_max(x,y) xv_set(x,PANEL_MAX_VALUE,y,NULL)
#define close_window(w) xv_set(w,XV_SHOW,FALSE,NULL)
#define open_window(w) xv_set(w,XV_SHOW,TRUE,NULL)

/* defines para os headers das funcoes callback */

#define notify_button(xxx) void xxx(Panel_item obj,Event* event)
#define notify_textfield(xxx) Panel_setting xxx(Panel_item obj,Event *event)
#define notify_setting(xxx) void xxx(Panel_item obj,int sel_setting,Event* event)
#define notify_menu(xxx) void xxx(Menu obj,Menu_item sel_menu)
#define event_canvas(xxx) void xxx(Xv_window window,Event *event)
#define notify_canvas(xxx) void xxx(Canvas obj,Xv_Window paint_window,Display* dpy,Window xwin,Xv_xrectlist* xrects)

Cms cms;
GC Ggc,Fgc,Rgc;
Display* Gdisplay;
Display* Fdisplay;
Display* Rdisplay;
Window Gxid,Fxid,Rxid;
int Fpronto=0,Rpronto=0;

short closed_bits[]= {
#include "ifft.icon"
};
Server_image closed_image;
Icon icon;

typedef enum {
  FonteV,VCVS,CCVS,CCCS,Capacitor,Resistor,FonteF,Amplificador,MOS,
  BJT,Girador,Indutor,Transformador,VCCS,FonteI,AmpOp
} componente;

typedef struct elemento {
  componente tipo;
  char nome[tamnome+1];
  short no[6];
  double val[4];
} elemento;

typedef double polinomio[Grmax+1];
typedef double raizes[Grmax];
typedef double curva[xxmax+1];

typedef struct fdet {
  char nome[256];
  short ngrau,dgrau;
  polinomio Num,Den;
  double cted,cten,fator;   /*fator de normalizacao em frequencia*/
  short ga,fa,ta;
  curva Gan,Fas,Tg;
  boolean numerador_valido,denominador_valido,zeros_validos,polos_validos;
  raizes RePolos,ImPolos,ReZeros,ImZeros;
} fdet;

typedef elemento ListaNet[MaxEl];
typedef unsigned long* cores;

typedef struct _REC_biblioteca {
  char letra;
  char nnos;
  char nmno[4][3];
  char nval;
  char nmval[4][4];
} _REC_biblioteca;

#define primeiro_tipo   FonteV
#define ultimo_tipo     AmpOp
#define cor_fraca       6

double wmin0=0.2,wmax0=5.0,gmin0=-80.0,gmax0=10.0;
short nref=0;
boolean netlist_lido=false,analise_feita=false,
	       resposta_plotada=false,raizes_plotadas=false;

_REC_biblioteca biblioteca[16]={
  { 'V',2,
    { "V+","V-","","" },
    1,
    { "V","","","" } },
  { 'E',4,
    { "V+","V-","v+","v-" },
    1,
    { "Av","","","" } },
  { 'H',4,
    { "V+","V-","i+","i-" },
    1,
    { "Rm","","","" } },
  { 'F',4,
    { "I+","I-","i+","i-" },
    1,
    { "Ai","","","" } },
  { 'C',2,
    { "a","b","","" },
    1,
    { "C","","","" } },
  { 'R',2,
    { "a","b","","" },
    1,
    { "R","","","" } },
  { 'Z',2,
    { "V-","V+","","" },
    2,
    { "Rs","Vs","","" } },
  { 'A',3,
    { "e-","e+","s","" },
    2,
    { "GB","Ro","","" } },
  { 'M',3,
    { "d","g","s","" },
    2,
    { "Gm","Gds","","" } },
  { 'Q',3,
    { "c","b","e","" },
    4,
    { "hfe","hie","hre","hoe" } },
  { 'Y',4,
    { "11","12","21","22" },
    1,
    { "Rg","","","" } },
  { 'L',2,
    { "a","b","","" },
    1,
    { "L","","","" } },
  { 'N',4,
    { "11","12","21","22" },
    4,
    { "L11","L22","M12","M21" } },
  { 'G',4,
    { "I+","I-","V+","V-" },
    1,
    { "Gm","","","" } },
  { 'I',2,
    { "I+","I-","","" },
    1,
    { "Is","","","" } },
  { 'O',3,
    { "ea","eb","s","" },
    0,
    { "","","","" } }
};

cores cor;
ListaNet netlist;
short C[MaxNosAntes+1],L[MaxNosAntes+1];
double Yr[MaxNos+1][MaxNos1+1],Yi[MaxNos+1][MaxNos1+1];
double Nr[MaxNos][MeioGm+1],Ni[MaxNos][MeioGm+1];
double Dr[MeioGm+1],Di[MeioGm+1];
double Frq[xxmax+1];
polinomio AA,BB;
Xv_opaque menu1,menu2,menu3,botao,bmais,jfrequencia,
		 cfrequencia,jparametros,tdispden,tdispnum,tfatorw,
		 tfatorz,tngrau,tdgrau,tsaida,sforcar,sraizes,
		 jextra,ttol,ttolm,treal,timag,tminimo,smetodo,
		 jpfrequencia,twmin,twmax,tgmin,
		 tgmax,tfmin,tfmax,tamin,tamax,slog,srads,
		 splotar,snorm,tsegmentos,jedit,tenome;
Xv_opaque tvalor[4],panel;
Xv_opaque jraizes,craizes,jreferencia,ttitulo,tnsaida,
	  tnumerador,tdenominador,tpolos,tzeros,jdiretorio,
	  tnetlist,jsweep,tswval,tswel,
          ssweep,tswmin,tswmax,tswn,sescala,jmontecarlo,
	  tmonten,tmontetr,tmontetlcm,sdistribuicao;
short iii,nos,nosantes,nosmesmo,numero,ind,graufft,ordem,eedit;
double Imag,fatorz,fatord,ang,sr,si,vr,vi,mden,fwd,fzd;
FILE *arquivo;
boolean ok,numerador;
char rede[256],txt[256];
fdet *funcao[maxref+1];
char r;
double DoisPi,LnDb,RadGraus;
short i;

double ah,bh,ag,bg,af,bf,at,bt,aw,bw,dx,w,a1,a2,b1,b2,
	      da1,da2,db1,db2,f,t1,t2,t;
short xa,xq,yq,atual,ultpt,ix,csr,xmin,xmax,ymin,ymax,xpmax,
	     ypmax,c_cursor;

/*polos e zeros*/
double immin,remin,delta,ay,by,ax,bx;
short basex,basey;
boolean polos;
char unid[2][5]={"Hz","rd/s"};

boolean modo1=true;

notify_textfield(InvalidarAnalise);

/* Sprites */

int xant[2], yant[2];

void PutSprite(int x,int y,int c)
{
  XSetFunction(Gdisplay,Ggc,GXxor);
  XSetForeground(Gdisplay,Ggc,c_cursor);
  XDrawRectangle(Gdisplay,Gxid,Ggc,xant[c]-5,yant[c]-5,10,10);
  XDrawRectangle(Gdisplay,Gxid,Ggc,x-5,y-5,10,10);
  XSetFunction(Gdisplay,Ggc,GXcopy);
  xant[c]=x;
  yant[c]=y;
}

void ResetSprite(int c)
{ 
  xant[c]=-100;
  yant[c]=-100;
}

/*Distribuicao Gaussiana com variancia unitaria (Numerical Recipes)*/

short iset=0;
double gset;

double RandGauss(void)
{
  double fac,r,v1,v2;

  if (iset==0) {
    do {
      v1=2*RANDOM-1;
      v2=2*RANDOM-1;
      r=v1*v1+v2*v2;
    } while (r>=1 || r==0);
    fac=sqrt(-2*log(r)/r);
    gset=v1*fac;
    iset=1;
    return (v2*fac);
  } else {
    iset=0;
    return gset;
  }
}

void ErroFatal(char *texto)
{
   notice_prompt(jfrequencia,NULL,
      NOTICE_MESSAGE_STRINGS,"Error",texto,"IFFT will quit",NULL,
      NOTICE_BUTTON,"Ok",1000,
    NULL);
  puts("IFFT interrupted");
  exit(1);
}
 
void Inverter(Xv_opaque obj,int b)
{
  set_sel(obj,get_sel(obj) ^ b);
}

boolean Teste(Xv_opaque obj,int b)
{
  return ((get_sel(obj) & b)==b);
}

boolean Log(void)
{
  return (get_sel(slog)==0);
}

boolean Rads(void)
{
  return (get_sel(srads)==0);
}

boolean Normalizar(void)
{
  return (get_sel(snorm)==0);
}

void InicializaRaizes(void)
{
  /*Usa o fator de normalizacao para setar a escala inicial*/
  if (Normalizar()) remin=-2.0;
  else remin=-get_real(tfatorw)*2;
  immin=remin;
  delta=-2*immin;
}
 
char *NomeAtual(char *Result,short atual)
{
  short i;
  fdet *WITH;

  WITH=funcao[atual];
  i=strlen(WITH->nome);
  while (i>0 && WITH->nome[i-1]!='/')
    i--;
  strcpy(txt,WITH->nome+i);
  if (atual>0)
    sprintf(txt+strlen(txt)," (#%d)",(int)atual);
  return strcpy(Result,txt);
}

double Cmult(double x1,double x2,double y1,double y2)
{
  Imag=x1*y2+x2*y1;
  return x1*y1-x2*y2;
}

double Ex(double x,double t)
{
  return exp(t*log(x));
}

/* Versao alternativa para XDrawRectangle */

void quadrado(int x,int y,int dx,int dy)
{
  XDrawLine(Gdisplay,Gxid,Ggc,x,y,x+dx,y);
  XDrawLine(Gdisplay,Gxid,Ggc,x+dx,y,x+dx,y+dy);
  XDrawLine(Gdisplay,Gxid,Ggc,x+dx,y+dy,x,y+dy);
  XDrawLine(Gdisplay,Gxid,Ggc,x,y+dy,x,y);
}

#define XDrawXDrawRectangle(Gdisplay,Gxid,Ggc,gd,gx,gg,x,y,dx,dy) quadrado(x,y,dx,dy)

short pos(char c,char* str2)
{
   char* res;
   res=strchr(str2,c);
   if (res==NULL) return 0;
   else return res-str2+1;
}

#define maxteste        19

typedef struct _REC_prioridade {
  componente cmp;
  char tr1,tr2,lado;
} _REC_prioridade;


/* Local variables for AcharOrdem: */
struct LOC_AcharOrdem {

  boolean ok;
  short arvore[MaxNosAntes+1];
  unsigned short marcado[MaxEl];
  short nosarvore,e;
} ;

void TentarIncluir(short no1,short no2,short ramo,struct LOC_AcharOrdem *LINK)
{
  short i;
  boolean um,dois;
  short FORLIM;
  elemento *WITH;

  if ((LINK->marcado[LINK->e-1] & ramo)==ramo)
    return;
  um=false;
  dois=false;
  FORLIM=LINK->nosarvore;
  for (i=0; i<=FORLIM; i++) {
    if (LINK->arvore[i]==L[no1])
      um=true;
    if (LINK->arvore[i]==L[no2])
      dois=true;
  }
  if (!(um ^ dois))
    return;
  LINK->nosarvore++;
  LINK->ok=true;
  if (um)
    LINK->arvore[LINK->nosarvore]=L[no2];
  else
    LINK->arvore[LINK->nosarvore]=L[no1];
  LINK->marcado[LINK->e-1]+=ramo;
  WITH=&netlist[LINK->e-1];
  printf("%s,nodes %d and %d\n",
	  WITH->nome,no1,no2);
}

void AcharOrdem(void)
{
  struct LOC_AcharOrdem V;

  _REC_prioridade prioridade[maxteste]={
    { FonteV,1,2,1 },
    { CCVS,3,4,1 },
    { CCCS,3,4,1 },
    { Capacitor,1,2,1 },
    { VCVS,1,2,1 },
    { CCVS,1,2,2 },
    { FonteF,1,2,1 },
    { Amplificador,3,0,1 },
    { BJT,2,3,1 },
    { Resistor,1,2,1 },
    { BJT,1,3,2 },
    { MOS,1,3,1 },
    { Girador,1,2,1 },
    { Girador,3,4,2 },
    { VCCS,1,2,2 },
    { CCCS,1,2,2 },
    { Indutor,1,2,1 },
    { Transformador,1,2,1 },
    { Transformador,3,4,2 }
  };

  short nosreais,tipo_em_teste,graudefault,FORLIM;
  _REC_prioridade *WITH;
  elemento *WITH1;

  V.nosarvore=0;
  V.arvore[0]=0;
  nosreais=nos-nosantes+nosmesmo;
  FORLIM=numero;
  for (V.e=1; V.e<=FORLIM; V.e++)
    V.marcado[V.e-1]=0;
  puts("Normal tree branches:");
  do {
    tipo_em_teste=1;
    do {
      V.e=1;
      V.ok=false;
      WITH=&prioridade[tipo_em_teste-1];
      do {
	WITH1=&netlist[V.e-1];
	if (WITH1->tipo==WITH->cmp)
	  TentarIncluir(WITH1->no[WITH->tr1-1],WITH1->no[WITH->tr2-1],
			WITH->lado,&V);
	V.e++;
      } while (!(V.e>numero || V.ok));
      tipo_em_teste++;
    } while (!(V.ok || tipo_em_teste>maxteste));
    if (!V.ok && tipo_em_teste>maxteste)
      puts("* Part of the network is floating");
  } while (V.nosarvore!=nosreais && tipo_em_teste<=maxteste);
  graudefault=0;
  ind=0;
  FORLIM=numero;
  for (V.e=1; V.e<=FORLIM; V.e++) {
    WITH1=&netlist[V.e-1];
    switch (WITH1->tipo) {

    case Capacitor:
      if (V.marcado[V.e-1]==1)
	graudefault++;
      break;

    case Indutor:
      ind++;
      if (V.marcado[V.e-1]==0)
	graudefault++;
      break;

    case Amplificador:
      graudefault++;
      ind++;
      break;

    case Transformador:
      if (V.marcado[V.e-1]==0)
	graudefault+=2;
      else if (V.marcado[V.e-1]<3)
	graudefault++;
      ind+=2;
      break;

    default:;
    }
  }
  printf("Maximum complexity order: %d\n",graudefault);
  printf("Number of elements in 1/s: %d\n",ind);
  set_int(tdgrau,graudefault);
  set_int(tngrau,graudefault);
}

#undef maxteste

void TestarNos(void)
{
   char STR2[256];

  if (nosantes>MaxNosAntes) {
    sprintf(STR2,"The maximum number of nodes is %d\n",MaxNosAntes);
    ErroFatal(STR2);
  }
}

void LerNetList(void)
{
  boolean leutudo;
  componente cp;
  short i,a1,b1,c1;
  char STR2[256];
  elemento *WITH;
  _REC_biblioteca *WITH1;
  short FORLIM1;
  int TEMP;

  netlist_lido=false;
  fscanf(arquivo,"%hd%*[^\n]",&nosantes);
  getc(arquivo);
  nos=nosantes;
  nosmesmo=nos;
  printf("Circuit: %s\n",rede);
  printf("Number of nodes: %d\n",nosmesmo);
  TestarNos();
  for (i=0; i<=MaxNosAntes; i++) {
    C[i]=i;
    L[i]=i;
  }
  puts("Circuit description:");
  numero=1;
  ind=0;
  while (fscanf(arquivo,"%s",STR2)!=EOF) {
    if (numero>MaxEl) {
      sprintf(STR2,"The maximum number of effective elements is %d\n",MaxEl);
      ErroFatal(STR2);
    }
    WITH=&netlist[numero-1];
    STR2[5]='\0';
    strcpy(WITH->nome,STR2);
    for (cp=primeiro_tipo;
	 (long)cp<=(long)ultimo_tipo;
	 cp=(componente)((long)cp+1)) {
      WITH1=&biblioteca[(long)cp];
      if (WITH->nome[0]==WITH1->letra) {
	leutudo=true;
	WITH->tipo=cp;
	FORLIM1=WITH1->nnos;
	for (i=0; i<FORLIM1; i++) {
	  fscanf(arquivo,"%d",&TEMP);
	  WITH->no[i]=TEMP;
	}
	FORLIM1=WITH1->nval;
	for (i=0; i<FORLIM1; i++)
          /* Assim tem que existir todos os parametros */
	  fscanf(arquivo,"%lg",&WITH->val[i]);
	fscanf(arquivo,"%*[^\n]");
	getc(arquivo);
	sprintf(txt,"%s: ",WITH->nome);
	/* Casos especiais */
	switch (WITH->tipo) {
        
        /*
	case FonteF:
	  if (!leutudo)
	    WITH->val[1]=1.0;
	  break;

	case Transformador:
	  if (!leutudo)
	    WITH->val[3]=WITH->val[2];
	  break;
        */

	case FonteV:
	case VCVS:
	case CCCS:
	  nosantes++;
	  nos++;
	  TestarNos();
	  WITH->no[4]=nosantes;
	  sprintf(txt+strlen(txt),"%d(j) ",nosantes);
	  break;

	case CCVS:
	  nosantes+=2;
	  nos+=2;
	  TestarNos();
	  WITH->no[4]=nosantes-1;
	  WITH->no[5]=nosantes;
	  sprintf(txt+strlen(txt),"%d(j1) %d(j2) ",WITH->no[4],WITH->no[5]);
	  break;

        default:;
	}
	FORLIM1=WITH1->nnos;
	for (i=0; i<FORLIM1; i++)
	  sprintf(txt+strlen(txt),"%d(%s) ",WITH->no[i],WITH1->nmno[i]);
	FORLIM1=WITH1->nval;
	for (i=0; i<FORLIM1; i++)
	  sprintf(txt+strlen(txt),"%s:%g ",
		  WITH1->nmval[i],WITH->val[i]);
	puts(txt);
	goto _LAchou;
      }
    }
    printf("* Unknown element: %s\n",WITH->nome);
    goto _LFim;
_LAchou:
    if (WITH->tipo!=AmpOp)
      numero++;
    else {
      if (C[WITH->no[0]]>C[WITH->no[1]]) {
	a1=C[WITH->no[1]];
	b1=C[WITH->no[0]];
      } else {
	a1=C[WITH->no[0]];
	b1=C[WITH->no[1]];
      }
      c1=L[WITH->no[2]];
      if (a1==b1 || c1==0)
	ErroFatal("Invalid circuit");
      for (i=1; i<=MaxNosAntes; i++) {
	if (C[i]==b1)
	  C[i]=a1;
	if (C[i]>b1)
	  C[i]--;
	if (L[i]==c1)
	  L[i]=0;
	if (L[i]>c1)
	  L[i]--;
      }
      nos--;
    }
  }
  numero--;
  printf("Number of effective elements: %d\n",numero);
  printf("Number of independent variables: %d\n",nos);
  if (nos>MaxNos) {
    sprintf(STR2,"The maximum number of independent variables is %d\n",MaxNos);
    ErroFatal(STR2);
  }
  AcharOrdem();
  netlist_lido=true;
  set_max(tsaida,nosantes);
  eedit=1;
  close_window(jedit);
  close_window(jsweep);
  WITH=&netlist[eedit-1];
  WITH1=&biblioteca[(long)WITH->tipo];
  xv_set(tenome,PANEL_LABEL_STRING,WITH->nome,NULL);
  for (i=0; i<=3; i++) {
    if (i+1<=WITH1->nval) {
      set_real(tvalor[i],WITH->val[i]);
      xv_set(tvalor[i],PANEL_LABEL_STRING,WITH1->nmval[i],NULL);
    } else {
      set_real(tvalor[i],0.0);
      xv_set(tvalor[i],XV_LABEL,"-",NULL);
    }
  }
  InvalidarAnalise(NULL,NULL);
_LFim:
  if (arquivo!=NULL)
    fclose(arquivo);
  arquivo=NULL;
}

void TransAdmitancia(double a,double b,short n1,short n2,short n3,short n4,boolean norm)
{
  if (norm) {
    a*=fatorz;
    b*=fatorz;
  }
  Yr[L[n1]][C[n3]]+=a;
  Yr[L[n2]][C[n4]]+=a;
  Yr[L[n1]][C[n4]]-=a;
  Yr[L[n2]][C[n3]]-=a;
  Yi[L[n1]][C[n3]]+=b;
  Yi[L[n2]][C[n4]]+=b;
  Yi[L[n1]][C[n4]]-=b;
  Yi[L[n2]][C[n3]]-=b;
}

void Admitancia(double a,double b,short n1,short n2)
{
  TransAdmitancia(a,b,n1,n2,n1,n2,true);
}

void Corrente(double I,short a,short b)
{
  Yr[L[a]][nos+1]-=I;
  Yr[L[b]][nos+1]+=I;
}

void Gyrator(short a,short b,short c)
{
  TransAdmitancia(1.0,0.0,a,b,c,0,false);
  TransAdmitancia(1.0,0.0,0,c,a,b,false);
}

void MontarSistema(void)
{
  short i,j;
  double t,t1;
  short FORLIM,FORLIM1;
  elemento *WITH;

  FORLIM=nos;
  for (i=0; i<=FORLIM; i++) {
    FORLIM1=nos+1;
    for (j=0; j<=FORLIM1; j++) {
      Yr[i][j]=0.0;
      Yi[i][j]=0.0;
    }
  }
  FORLIM=numero;
  for (i=0; i<FORLIM; i++) {
    WITH=&netlist[i];
    switch (WITH->tipo) {

    case Resistor:
      Admitancia(1/WITH->val[0],0.0,WITH->no[0],WITH->no[1]);
      break;

    case Indutor:
      t=WITH->val[0]*(sr*sr+si*si);
      Admitancia(sr/t,-(si/t),WITH->no[0],WITH->no[1]);
      break;

    case Capacitor:
      Admitancia(sr*WITH->val[0],si*WITH->val[0],WITH->no[0],
		 WITH->no[1]);
      break;

    case Amplificador:
      /* Y12=-GB/sRo; Y22=1/Ro */
      Admitancia(1/WITH->val[1],0.0,WITH->no[2],0);
      t=WITH->val[0]/WITH->val[1]/(sr*sr+si*si);
      TransAdmitancia(t*sr,-t*si,0,WITH->no[2],WITH->no[1],
		      WITH->no[0],true);
      break;

    case VCCS:
      TransAdmitancia(WITH->val[0],0.0,WITH->no[0],WITH->no[1],
		      WITH->no[2],WITH->no[3],true);
      break;

    case FonteF:  /*Fonte com resistor s‚rie*/
      Corrente(fatorz*WITH->val[1]/WITH->val[0],WITH->no[0],WITH->no[1]);
      Admitancia(1/WITH->val[0],0.0,WITH->no[0],WITH->no[1]);
      break;

    case FonteI:   /*Fonte de corrente*/
      Corrente(fatorz*WITH->val[0],WITH->no[0],WITH->no[1]);
      break;

    case Girador:
      /* Y12=1/R Y21=-1/R */
      TransAdmitancia(1/WITH->val[0],0.0,WITH->no[0],WITH->no[1],
		      WITH->no[2],WITH->no[3],true);
      TransAdmitancia(1/WITH->val[0],0.0,WITH->no[3],WITH->no[2],
		      WITH->no[0],WITH->no[1],true);
      break;

    case Transformador:
      /* Y11=L2/sDet(L) */
      /* Y22=L1/sDet(L) */
      /* Y12=-M12/sDet(L) */
      /* Y21=-M21/sDet(L) */
      t=(WITH->val[0]*WITH->val[1]-WITH->val[2]*WITH->val[3]) *
	  (sr*sr+si*si);
      t1=WITH->val[1]/t;   /*Y11*/
      Admitancia(t1*sr,-t1*si,WITH->no[0],WITH->no[1]);
      t1=WITH->val[0]/t;   /*Y22*/
      Admitancia(t1*sr,-t1*si,WITH->no[2],WITH->no[3]);
      t1=-(WITH->val[2]/t);   /*Y12*/
      TransAdmitancia(t1*sr,-t1*si,WITH->no[0],WITH->no[1],
		      WITH->no[2],WITH->no[3],true);
      t1=-(WITH->val[3]/t);   /*Y21*/
      TransAdmitancia(t1*sr,-t1*si,WITH->no[2],WITH->no[3],
		      WITH->no[0],WITH->no[1],true);
      break;

    case MOS:
      /*Gm*/
      TransAdmitancia(WITH->val[0],0.0,WITH->no[0],WITH->no[2],
		      WITH->no[1],WITH->no[2],true);
      /*Gds*/
      Admitancia(WITH->val[1],0.0,WITH->no[0],WITH->no[2]);
      break;

    case BJT:
      Admitancia(1/WITH->val[1],0.0,WITH->no[1],WITH->no[2]);   /*hie*/
      Admitancia(WITH->val[3],0.0,WITH->no[0],WITH->no[2]);   /*hoe*/
      TransAdmitancia(WITH->val[0]/WITH->val[1],0.0,WITH->no[0],
		      WITH->no[2],WITH->no[1],WITH->no[2],true);
	  /*hfe/hie*/
      TransAdmitancia(WITH->val[2]/WITH->val[1],0.0,WITH->no[2],
		      WITH->no[1],WITH->no[0],WITH->no[2],true);
	  /*hre/hie*/
      TransAdmitancia(WITH->val[2]*WITH->val[0]/WITH->val[1],0.0,
		      WITH->no[0],WITH->no[2],WITH->no[2],WITH->no[0],
		      true);
	  /*hre*hfe/hie*/
      break;

    case FonteV:
      Gyrator(WITH->no[0],WITH->no[1],WITH->no[4]);
      Corrente(WITH->val[0],WITH->no[4],0);
      break;

    case VCVS:
      Gyrator(WITH->no[0],WITH->no[1],WITH->no[4]);
      TransAdmitancia(WITH->val[0],0.0,WITH->no[4],0,WITH->no[2],
		      WITH->no[3],false);
      break;

    case CCCS:
      TransAdmitancia(WITH->val[0],0.0,WITH->no[0],WITH->no[1],
		      WITH->no[4],0,false);
      Gyrator(WITH->no[2],WITH->no[3],WITH->no[4]);
      break;

    case CCVS:
      TransAdmitancia(WITH->val[0]/fatorz,0.0,WITH->no[5],0,WITH->no[4],
		      0,false);
      Gyrator(WITH->no[0],WITH->no[1],WITH->no[5]);
      Gyrator(WITH->no[2],WITH->no[3],WITH->no[4]);
      break;

    default:
      puts("Something is wrong");
      exit(1);
    }
  }
}

void ResolverSistema(void)
{
  double qr,qi,tr,ti,t;
  short i,j,k,m,FORLIM,FORLIM1;
  char STR3[256];
  short FORLIM2;

  vr=cos(ind*ang);
  vi=sin(ind*ang);
  FORLIM=nos;
  for (i=1; i<=FORLIM; i++) {
    tr=0.0;
    ti=0.0;
    m=i;
    FORLIM1=nos;
    for (k=i; k<=FORLIM1; k++) {
      if (fabs(Yr[k][i])+fabs(Yi[k][i])>fabs(tr)+fabs(ti)) {
	m=k;
	tr=Yr[k][i];
	ti=Yi[k][i];
      }
    }
    if (i!=m) {
      vi=-vi;
      vr=-vr;
      FORLIM1=nos+1;
      for (k=i; k<=FORLIM1; k++) {
	t=Yr[i][k];
	Yr[i][k]=Yr[m][k];
	Yr[m][k]=t;
	t=Yi[i][k];
	Yi[i][k]=Yi[m][k];
	Yi[m][k]=t;
      }
    }
    vr=Cmult(vr,vi,tr,ti);
    vi=Imag;
    t=tr*tr+ti*ti;
    if (t==0) {
      sprintf(STR3,
	"Singular circuit for s=%g %gj\n  Use another freq. norm. factor if s is a pole",sr,si);
      ErroFatal(STR3);
    }
    for (j=nos+1; j>i; j--) {
      qr=(Yr[i][j]*tr+Yi[i][j]*ti)/t;
      qi=(Yi[i][j]*tr-Yr[i][j]*ti)/t;
      Yi[i][j]=qi;
      Yr[i][j]=qr;
      FORLIM2=nos;
      for (k=1; k<=FORLIM2; k++) {
	if (i!=k) {
	  Yr[k][j]-=Cmult(Yr[k][i],Yi[k][i],qr,qi);
	  Yi[k][j]-=Imag;
	}
      }
    }
  }
}

short Inverso(short x)
{
  /*Bit inverso*/
  short i,u;

  u=0;
  i=((unsigned)graufft)>>1;
  do {
    if (x & 1)
      u+=i;
    i=((unsigned)i)>>1;
    x=((unsigned)x)>>1;
  } while (x!=0);
  return u;
}

void FFT(void)
{
  /*"Fast Fourier Transform"*/
  short k1,m,k,j,u,i;
  double x1,y1,t;
  short FORLIM;

  for (k=ordem-1; k>=0; k--) {
    k1=(long)floor(Ex(2.0,(double)k)+0.5);
    m=0;
    do {
      j=Inverso(m/k1);
      x1=cos(DoisPi*j/graufft);
      y1=-sin(DoisPi*j/graufft);
      for (j=0; j<k1; j++) {
	u=j+m;
	i=u+k1;
	t=Cmult(AA[i],BB[i],x1,y1);
	AA[u]+=t;
	BB[u]+=Imag;
	AA[i]=AA[u]-t-t;
	BB[i]=BB[u]-Imag-Imag;
      }
      m+=k1 << 1;
    } while (m<graufft);
  }
  FORLIM=graufft;
  for (i=0; i<FORLIM; i++) {
    j=Inverso(i);
    if (j>i) {
      x1=AA[i];
      AA[i]=AA[j];
      AA[j]=x1;
    }
  }
  FORLIM=graufft;
  for (i=0; i<FORLIM; i++)
    AA[i] /= graufft;
}  /*FFT*/

void AnunciarRaizes(void)
{
  char STR1[256];

  if (numerador)
    strcpy(txt,"Zeros: ");
  else
    strcpy(txt,"Poles: ");
  sprintf(txt+strlen(txt),"%s,",NomeAtual(STR1,atual));
  if (get_sel(snorm)==1)
    strcat(txt,"un");
  printf("%snormalized\n",txt);
}

void ListarRaizes(short n0,double *Re,double *Im)
{
  short i;

  for (i=0; i<n0; i++) {
    if (fabs(Re[i])<get_real(tminimo))
      Re[i]=0.0;
    if (fabs(Im[i])<get_real(tminimo))
      Im[i]=0.0;
    sprintf(txt,"x(%d)=%g",i+1,fatord*Re[i]);
    if (Im[i]!=0) {
      if (Im[i]>0)
	strcat(txt," ");
      sprintf(txt+strlen(txt)," %gj",fatord*Im[i]);
    }
    puts(txt);
  }
}


#define imax            50


void Biv(short n0, double *a1_, double *Re, double *Im, boolean *raizes_validas)
{
  polinomio a1,a2,c1,c2;
  double tolm,t,tol,p1,p2,d,xr,xi,p,d1,d2,e1,e2;
  boolean feito;
  short i,j,nn,n,ordem;
  double TEMP,TEMP1;

  memcpy(a1,a1_,sizeof(polinomio));
  AnunciarRaizes();
  if (n0==0) {
    puts("No finite roots");
    return;
  }
  tol=get_real(ttol);
  tolm=get_real(ttolm);
  xr=get_real(treal);
  xi=get_real(timag);
  feito=false;
  ordem=0;
  nn=0;
  n=n0;
  for (i=0; i<=n; i++)
    a2[i]=0.0;
  /*Eliminacao de raizes na origem*/
  while (n>1 && a1[0]==0) {
    Re[n-1]=0.0;
    Im[n-1]=0.0;
    n--;
    for (i=0; i<=n; i++)
      a1[i]=a1[i+1];
  }
  while (!feito) {
    if (n>1) {
      /*Calculo dos valores do polinomio (p) e de sua derivada (d)*/
      d1=a1[n];
      p1=d1;
      d2=a2[n];
      p2=d2;
      for (i=n-1; i>=0; i--) {
	p1=Cmult(p1,p2,xr,xi)+a1[i];
	p2=Imag+a2[i];
	if (i>0) {
	  d1=Cmult(d1,d2,xr,xi)+p1;
	  d2=Imag+p2;
	}
      }
      /*Calculo do erro. Esta forma dificulta overflow*/
      if (d1==0 || d2==0) {
	d=d1*d1+d2*d2;
	e1=(p1*d1+p2*d2)/d;
	e2=(p2*d1-p1*d2)/d;
      } else {
	d=d1/d2+d2/d1;
	e1=(p1/d2+p2/d1)/d;
	e2=(p2/d2-p1/d1)/d;
      }
      /*Testa possivel raiz multipla*/
      d=fabs(d1)+fabs(d2);
      p=fabs(p1)+fabs(p2);
      if (d<tolm && p<tolm) {
	/*deriva o polinomio e continua*/
	if (ordem==0) {
	  memcpy(c1,a1,sizeof(polinomio));
	  memcpy(c2,a2,sizeof(polinomio));
	}
	for (i=1; i<=n; i++) {
	  a1[i-1]=a1[i]*i/n;
	  a2[i-1]=a2[i]*i/n;
	}
	n--;
	ordem++;
	continue;
      }
      /*Atualiza raizes*/
      xr-=e1;
      xi-=e2;
      /*Testa convergencia*/
      t=fabs(e1)+fabs(e2);
      if (t<tol) {
	/*Armazena raizes calculadas*/
	for (i=n+ordem-1; i>=n-1; i--) {
	  Re[i]=xr;
	  Im[i]=xi;
	}
	/*Repoe polinomio original,se for o caso*/
	if (ordem>0) {
	  memcpy(a1,c1,sizeof(polinomio));
	  memcpy(a2,c2,sizeof(polinomio));
	  n+=ordem;
	}
	/*Deflaciona polinomio*/
	for (i=0; i<=ordem; i++) {
	  for (j=n-1; j>=1; j--) {
	    a1[j]=Cmult(xr,xi,a1[j+1],a2[j+1])+a1[j];
	    a2[j]=Imag+a2[j];
	  }
	  n--;
	  for (j=0; j<=n; j++) {
	    a1[j]=a1[j+1];
	    a2[j]=a2[j+1];
	  }
	}
	/*Prepara ca lculo da pr¢xima raiz*/
	if (fabs(xi)>0.01)
	  xi=-xi;
	else
	  xi=0.1;
	if (ordem>0)   /*evita derivada 0 a seguir*/
	  xr-=0.01;
	ordem=0;
	nn=0;
	continue;
      }
      nn++;
      /*Demorando a convergir*/
      if (nn<=imax)
	continue;
      tol*=10;
      printf("*  Tolerance increased to %g\n",tol);
      nn=0;
      continue;
    }
    TEMP=a1[1];
    TEMP1=a2[1];
    /*Ultimas ra¡zes*/
    d=-(TEMP*TEMP+TEMP1*TEMP1);
    xr=(a1[0]*a1[1]+a2[0]*a2[1])/d;
    xi=(a2[0]*a1[1]-a1[0]*a2[1])/d;
    feito=true;
    nn=0;
    for (i=n+ordem-1; i>=n-1; i--) {
      Re[i]=xr;
      Im[i]=xi;
    }
  }
  *raizes_validas=true;
  ListarRaizes(n0,Re,Im);
}

#undef imax

#define imax            100

/* Local variables for Lib: */
struct LOC_Lib {
  double *Re,*Im;
  short n;
  double u,v,d;
} ;

void Resolve(LINK)
struct LOC_Lib *LINK;
{
  /*Calcula raizes de termo de 2o. grau*/
  LINK->d=LINK->u*LINK->u-4*LINK->v;
  if (LINK->d>=0) {
    LINK->Re[LINK->n-1]=(sqrt(LINK->d)-LINK->u)/2;
    LINK->Re[LINK->n-2]=(-LINK->u-sqrt(LINK->d))/2;
    LINK->Im[LINK->n-1]=0.0;
    LINK->Im[LINK->n-2]=0.0;
  } else {
    LINK->Re[LINK->n-1]=LINK->u/-2;
    LINK->Re[LINK->n-2]=LINK->u/-2;
    LINK->Im[LINK->n-1]=sqrt(-LINK->d)/2;
    LINK->Im[LINK->n-2]=-LINK->Im[LINK->n-1];
  }
  LINK->n-=2;
}

void Lib(n0,A_,Re_,Im_,raizes_validas)
short n0;
double *A_;
double *Re_,*Im_;
boolean *raizes_validas;
{
  struct LOC_Lib V;
  polinomio A;
  short i,j;
  double t,u1,v1,c1,c2,c3,t1;
  polinomio B;
  short FORLIM;

  memcpy(A,A_,sizeof(polinomio));
  V.Re=Re_;
  V.Im=Im_;
  AnunciarRaizes();
  if (n0==0) {
    puts("No finite roots");
    return;
  }
  V.n=n0;
  t=get_real(ttol);
  V.v=get_real(treal)*get_real(treal) +
	get_real(timag)*get_real(timag);
  V.u=-2*get_real(treal);
  while (A[0]==0 && V.n>1) {
    V.Re[V.n-1]=0.0;
    V.Im[V.n-1]=0.0;
    V.n--;
    FORLIM=V.n;
    for (j=0; j<=FORLIM; j++)
      A[j]=A[j+1];
  }
  do {
    if (V.n==1) {
      V.Re[0]=-(A[0]/A[1]);
      V.Im[0]=0.0;
      goto _LFim;
    }
    if (V.n==2) {
      V.u=A[1]/A[2];
      V.v=A[0]/A[2];
      Resolve(&V);
      goto _LFim;
    }
    i=0;
    do {
      if (i>imax) {
	t*=10;
	i=0;
	printf("* Tolerance increased to %g\n",t);
      }
      i++;
      B[V.n]=A[V.n];
      c2=B[V.n];
      B[V.n-1]=A[V.n-1]-V.u*B[V.n];
      c1=B[V.n-1]-V.u*c2;
      for (j=V.n-2; j>=1; j--) {
	c3=c2;
	c2=c1;
	B[j]=A[j]-V.u*B[j+1]-V.v*B[j+2];
	c1=B[j]-V.u*c2-V.v*c3;
      }
      B[0]=A[0]-V.u*B[1]-V.v*B[2];
      if (c1!=0 && c2!=0 && c3!=0) {
	u1=(B[0]/c2-B[1]/c3)/(c2/c3-c1/c2);
	v1=(B[1]/c2-B[0]/c1)/(c2/c1-c3/c2);
      } else {
	V.d=c2*c2-c1*c3;
	if (V.d==0) {
	  puts("* Impossible to find roots");
	  return;
	}
	u1=(B[0]*c3-B[1]*c2)/V.d;
	v1=(B[1]*c1-B[0]*c2)/V.d;
      }
      V.u-=u1;
      V.v-=v1;
      t1=fabs(u1)+fabs(v1);
    } while (t1>=t);
    Resolve(&V);
    FORLIM=V.n;
    for (j=0; j<=FORLIM; j++)
      A[j]=B[j+2];
  } while (true);
_LFim:
  *raizes_validas=true;
  ListarRaizes(n0,V.Re,V.Im);
}  /*Lib*/

#undef imax

void ApresentarPolinomio(grau,cte,Pol,polinomio_valido,
				raizes_validas)
short *grau;
double *cte;
double *Pol;
boolean *polinomio_valido,*raizes_validas;
{
  double maior,t,fw,fz,nively,dispersao;
  short i,menorgrau,correcaoj;
  char texto[256];
  short FORLIM;
  fdet *WITH;

  *polinomio_valido=false;
  *raizes_validas=false;
  correcaoj=0;
  if (numerador) {
    sprintf(texto,"Numerator,node %d",get_int(tsaida));
    if (get_int(tsaida)>nosmesmo) {
      strcat(texto," (current)");
      /*Os numeradores dos j sao multiplicados por fatorz uma vez a mais*/
      correcaoj=1;
    }
    strcat(texto,",");
    dispersao=get_real(tdispnum);
    *grau=get_int(tngrau);
  } else {
    strcpy(texto,"Denominator,");
    dispersao=get_real(tdispden);
    *grau=get_int(tdgrau);
  }
  if (!Normalizar())
    strcat(texto,"un");
  printf("%snormalized\n",texto);
  maior=0.0;
  FORLIM=graufft;
  for (i=0; i<FORLIM; i++) {
    if (fabs(AA[i])>maior)
      maior=fabs(AA[i]);
  }
  if (maior==0) {
    if (numerador) {
      puts("Zero: no signal");
      return;
    } else {
      puts("* Zero: bad impedance normalization");
      return;
    }
  }
  memcpy(Pol,AA,sizeof(polinomio));
  if (get_sel(sforcar)==1) {
    t=maior/dispersao;
    FORLIM=graufft;
    for (i=0; i<FORLIM; i++) {
      if (fabs(Pol[i])>t)
	*grau=i;
      else
	Pol[i]=0.0;
    }
  }
  menorgrau=0;
  while (Pol[menorgrau]==0 && menorgrau<*grau)
    menorgrau++;
  nively=Pol[*grau];
  if (nively==0) {
    puts("* The forced degree cannot be this");
    return;
  }
  FORLIM=*grau;
  for (i=0; i<=FORLIM; i++) {
    Pol[i] /= nively;
    printf("a(%d)=%g\n",i,Pol[i]*Ex(fatord,(double)(*grau-i)));
  }
  if (numerador) {
    *cte=nively/mden;
    if (correcaoj==1)
      *cte /= fatorz;
    WITH=funcao[0];
    printf("Cst= %g\n",*cte*Ex(fatord,(double)(WITH->dgrau-WITH->ngrau)));
  } else {
    mden=nively;
    *cte=1.0;
  }
  if (*grau>menorgrau) {   /*Haveria um valor ideal neste caso?*/
    fw=get_real(tfatorw)*Ex(fabs(Pol[menorgrau]),
					1.0/(*grau-menorgrau));
    nively*=Ex(get_real(tfatorw)/fw,(double)(ind-*grau));
  } else
    fw=0.0;
  /*Os elementos com girador introduzem 2 nos extra*/
  i=nos+(nosmesmo-nosantes)*2+correcaoj;
  if (i>0)
    fz=Ex(fabs(nively),-1.0/i)*fatorz;
  else
    fz=0.0;
  if (numerador) {
    printf("Used frequency normalization=%g\n",get_real(tfatorw));
    printf("Used impedance normalization=%g\n",get_real(tfatorz));
    if (fwd!=0)
      printf("Ideal f. n. for denominator= %g\n",fwd);
    if (fzd!=0) {
      printf("Ideal i. n. for denominator= %g\n",fzd);
      if (fwd==0)
	puts("(for the used f. n.)");
    }
    if (fw!=0)
      printf("Ideal f. n. for numerator=   %g\n",fw);
    if (fz!=0) {
      printf("Ideal i. n. for numerator=   %g\n",fz);
      if (fw==0)
	puts("(for the used f. n.)");
    }
  } else {
    fwd=fw;
    fzd=fz;
    if (*grau!=get_int(tdgrau)) {
      printf("* Complexity order differs from the expected (%d)\n",get_int(tdgrau));
      puts("  Verify analysis parameters (bad normalization?)");
      return;
    }
  }
  *polinomio_valido=true;
}

void AnalisarCircuito(void)
{
  short i,ii;
  char STR2[256];
  short FORLIM;

  InvalidarAnalise(NULL,NULL);
  graufft=1;
  while (graufft<=get_int(tdgrau) ||
	 graufft<=get_int(tngrau))
    graufft*=2;
  if (graufft>Grmax+1) {
    sprintf(STR2,"The maximum order is %d",Grmax);
    ErroFatal(STR2);
  }
  ordem=(long)floor(log((double)graufft)/log(2.0)+0.5);
  printf("Order for the interpolation: %d\n",graufft);
  printf("Analyzing...");
  FORLIM=((unsigned)graufft)>>1;
  for (ii=0; ii<=FORLIM; ii++) {
    ang=DoisPi*ii/graufft;
    sr=get_real(tfatorw)*cos(ang);
    si=get_real(tfatorw)*sin(ang);
    printf("%d ",(graufft>>1)-ii);
    MontarSistema();
    ResolverSistema();
    Dr[ii]=vr;
    Di[ii]=vi;
    for (i=1; i<=nos; i++) {
      Nr[i-1][ii]=Cmult(Yr[i][nos+1],Yi[i][nos+1],vr,vi);
      Ni[i-1][ii]=Imag;
    }
  }
  puts("");
  analise_feita=true;
}

void CalcularDenominador(void)
{
  short i,k,FORLIM;
  fdet *WITH;

  FORLIM=((unsigned)graufft)>>1;
  for (i=0; i<=FORLIM; i++) {
    k=(graufft-i) % graufft;
/* p2c: ifft.pas,line 1033:
*Note: Using % for possibly-negative arguments [317] */
    AA[i]=Dr[i];
    AA[k]=Dr[i];
    BB[i]=Di[i];
    BB[k]=-Di[i];
  }
  FFT();
  WITH=funcao[0];
  ApresentarPolinomio(&WITH->dgrau,&WITH->cted,WITH->Den,
		      &WITH->denominador_valido,&WITH->polos_validos);
}

void CalcularNumerador(void)
{
  short i,k;
  fdet *WITH;
  short FORLIM;

  WITH=funcao[0];
  if (C[get_int(tsaida)]==0) {
    printf("* Node %d is real/virtual ground\n",get_int(tsaida));
    WITH->numerador_valido=false;
  } else {
    FORLIM=((unsigned)graufft)>>1;
    for (i=0; i<=FORLIM; i++) {
      k=(graufft-i) % graufft;
/* p2c: ifft.pas,line 1053:
*Note: Using % for possibly-negative arguments [317] */
      AA[i]=Nr[C[get_int(tsaida)]-1][i];
      AA[k]=AA[i];
      BB[i]=Ni[C[get_int(tsaida)]-1][i];
      BB[k]=-BB[i];
    }
    FFT();
    ApresentarPolinomio(&WITH->ngrau,&WITH->cten,WITH->Num,
			&WITH->numerador_valido,&WITH->zeros_validos);
  }
  sprintf(WITH->nome,"%s n%d",rede,get_int(tsaida));
  if (!WITH->numerador_valido) {
    WITH->ngrau=0;
    WITH->cten=0.0;
  }
}

void SalvarPolinomio(char *nome, short grau, double cte, double fator, double *pol)
{
  short i;

  arquivo=fopen(nome,"w");
  fprintf(arquivo,"%d\n",grau);
  for (i=0; i<=grau; i++)
    fprintf(arquivo,"% .5E\n",pol[i]);
  fprintf(arquivo,"% .5E\n",cte);
  fprintf(arquivo,"% .5E\n",fator);
  fclose(arquivo);
  printf("Normalized polynomial saved in file %s\n",nome);
}

void SalvarRaizes(char *nome, short grau, double cte, double fator, double *Re, double *Im)
{
  short i;

  arquivo=fopen(nome,"w");
  fprintf(arquivo,"%d\n",grau);
  for (i=0; i<grau; i++)
    fprintf(arquivo,"% .5E % .5E\n",Re[i],Im[i]);
  fprintf(arquivo,"% .5E\n",cte);
  fprintf(arquivo,"% .5E\n",fator);
  fclose(arquivo);
  printf("Normalized roots saved in file %s\n",nome);
}

boolean AbrirArquivo(char *nome)
{
  if (*nome=='\0') return false;
  arquivo=fopen(nome,"r");
  if (arquivo==0) {
    printf("* File %s not found\n",nome);
    return false;
  }
  else return true;
}

void LerFinal(double *cte, double *fator)
{
  if (fscanf(arquivo,"%lg%*[^\n]",cte)!=EOF)
    getc(arquivo);
  else
    *cte=1.0;
  if (fscanf(arquivo,"%lg%*[^\n]",fator)!=EOF)
    getc(arquivo);
  else
    *fator=1.0;
  printf("Cst=%g\nNorm. factor=%g\n",*cte,*fator);
  fclose(arquivo);
}

boolean LerPolinomio(nome,grau,cte,fator,pol)
char *nome;
short *grau;
double *cte,*fator;
double *pol;
{
  short i;

  if (AbrirArquivo(nome)) {
    printf("Reading polynomial from file %s\n",nome);
    fscanf(arquivo,"%hd%*[^\n]",grau);
    getc(arquivo);
    printf("Degree: %d\n",*grau);
    for (i=0; i<=*grau; i++) {
      fscanf(arquivo,"%lg%*[^\n]",&pol[i]);
      getc(arquivo);
      printf("a(%d)=%g\n",i,pol[i]);
    }
    LerFinal(cte,fator);
    return true;
  } else
    return false;
}

boolean LerRaizes(nome,grau,cte,fator,Re,Im)
char *nome;
short *grau;
double *cte,*fator;
double *Re,*Im;
{
  short i;

  if (AbrirArquivo(nome)) {
    printf("Reading roots from file %s\n",nome);
    fscanf(arquivo,"%hd%*[^\n]",grau);
    getc(arquivo);
    for (i=0; i<*grau; i++) {
      fscanf(arquivo,"%lg%lg%*[^\n]",&Re[i],&Im[i]);
      getc(arquivo);
      printf("x(%d)=%g\n",i+1,Re[i]);
      if (Im[i]!=0) {
	printf("     %gj\n",Im[i]);
      }
    }
    LerFinal(cte,fator);
    return true;
  } else
    return false;
}

boolean AlocarReferencia()
{
  if (nref<maxref) {
    nref++;
    if ((funcao[nref]=(fdet *)malloc(sizeof(fdet)))!=NULL) {
      printf("Reference #%d created\n",nref);
      return true;
    } else {
      nref--;
      puts("* Insufficient memory");
      return false;
    }
  } else {
    puts(" Too many references");
    return false;
  }
}

void DesalocarReferencia()
{
  if (nref<=0) {
    puts("* No references stored");
    return;
  }
  printf("Reference #%d eliminated\n",nref);
  free(funcao[nref]);
  nref--;
  atual=0;
}

void CalcularPolosEZeros()
{
  fdet *WITH;

  WITH=funcao[atual];
  if (Normalizar())
    fatord=1.0;
  else
    fatord=WITH->fator;
  if (WITH->denominador_valido) {
    numerador=false;
    if (!WITH->polos_validos) {
      if (get_sel(smetodo)==1)
	Biv(WITH->dgrau,WITH->Den,WITH->RePolos,WITH->ImPolos,
	    &WITH->polos_validos);
      else
	Lib(WITH->dgrau,WITH->Den,WITH->RePolos,WITH->ImPolos,
	    &WITH->polos_validos);
    }
  } else
    puts("* No denominator computed");
  if (!WITH->numerador_valido) {
    puts("* No numerator computed");
    return;
  }
  numerador=true;
  if (WITH->zeros_validos)
    return;
  if (get_sel(smetodo)==1)
    Biv(WITH->ngrau,WITH->Num,WITH->ReZeros,WITH->ImZeros,
	&WITH->zeros_validos);
  else
    Lib(WITH->ngrau,WITH->Num,WITH->ReZeros,WITH->ImZeros,
	&WITH->zeros_validos);
}

void ZoomOut()
{
  set_real(twmin,wmin0);
  set_real(twmax,wmax0);
  set_real(tgmin,gmin0);
  set_real(tgmax,gmax0);
}
 
void PrepararAnalise(void)
{
  if (netlist_lido)
    open_window(jparametros);
  else
    puts("* No netlist read");
}

notify_button(IniciarAnalise)
{
  close_window(jparametros);
  fatorz=get_real(tfatorz);
  if (Normalizar())
    fatord=1.0;
  else
    fatord=get_real(tfatorw);
  funcao[0]->fator=get_real(tfatorw);
  if (!analise_feita)
    AnalisarCircuito();
  atual=0;
  numerador=false;
  if (!funcao[0]->denominador_valido)
    CalcularDenominador();
  if (!funcao[0]->denominador_valido)
    return;
  numerador=true;
  if (!funcao[0]->numerador_valido)
    CalcularNumerador();
  if (get_sel(sraizes)==0)
    CalcularPolosEZeros();
  if (funcao[0]->numerador_valido)
    open_window(jpfrequencia);
}

notify_textfield(InvalidarNumerador)
{
  fdet *WITH;

  WITH=funcao[0];
  WITH->numerador_valido=false;
  WITH->zeros_validos=false;
  *WITH->nome='\0';
  raizes_plotadas=false;
  resposta_plotada=false;
  return PANEL_NEXT;
}

notify_textfield(InvalidarDenominador)
{
  fdet *WITH;

  WITH=funcao[0];
  WITH->denominador_valido=false;
  WITH->polos_validos=false;
  InvalidarNumerador(NULL,NULL);
  return PANEL_NEXT;
}

notify_textfield(InvalidarRaizes)
{
  fdet *WITH;

  WITH=funcao[0];
  WITH->polos_validos=false;
  WITH->zeros_validos=false;
  raizes_plotadas=false;
  return PANEL_NEXT;
}

notify_textfield(InvalidarAnalise)
{
  analise_feita=false;
  InvalidarDenominador(NULL,NULL);
  return PANEL_NEXT;
}

notify_button(MudarElemento)
{
  short i;
  elemento *WITH;
  _REC_biblioteca *WITH1;

  if (obj==bmais)
    eedit++;
  else
    eedit--;
  if (eedit>numero)
    eedit=1;
  else if (eedit<1)
    eedit=numero;
  WITH=&netlist[eedit-1];
  WITH1=&biblioteca[(long)WITH->tipo];
  xv_set(tenome,PANEL_LABEL_STRING,WITH->nome,NULL);
  for (i=0; i<=3; i++) {
    if (i+1<=WITH1->nval) {
      set_real(tvalor[i],WITH->val[i]);
      xv_set(tvalor[i],PANEL_LABEL_STRING,WITH1->nmval[i],NULL);
    } else {
      set_real(tvalor[i],0.0);
      xv_set(tvalor[i],PANEL_LABEL_STRING,"-",NULL);
    }
  }
}

notify_textfield(AlterarValor)
{
  short i;
  elemento *WITH;
  _REC_biblioteca *WITH1;

  if (eedit>0) {
    WITH=&netlist[eedit-1];
    WITH1=&biblioteca[(long)WITH->tipo];
    for (i=0; i<=3; i++) {
      if (obj==tvalor[i]) {
	WITH->val[i]=get_real(tvalor[i]);
	InvalidarAnalise(NULL,NULL);
      }
    }
  }
  open_window(jparametros);
  return PANEL_NEXT;
}

notify_textfield(AbrirNetList)
{
  if (pos('.',get_text(tnetlist))==0) strcat(get_text(tnetlist),".net");
  sprintf(rede,"%.*s",
	  pos('.',get_text(tnetlist))-1,
	  get_text(tnetlist));
  if (!AbrirArquivo(get_text(tnetlist))) return PANEL_NEXT;
  LerNetList();
  close_window(jdiretorio);
  PrepararAnalise();
  return PANEL_NEXT;
}

void TracarEscalas()
{
  short i,j;
  
  XSetForeground(Gdisplay,Ggc,cor[0]);
  XFillRectangle(Gdisplay,Gxid,Ggc,0,0,xmin-1,ymax);
  i=xmin-30;
  j=(ymax+ymin)/2-4;
  if (Teste(splotar,4)) {
    XSetForeground(Gdisplay,Ggc,cor[2]);
    sprintf(txt,"%7.2f",get_real(tamax));
    XDrawString(Gdisplay,Gxid,Ggc,0,ymin+40,txt,strlen(txt));
    sprintf(txt,"%7.2f",get_real(tamin));
    XDrawString(Gdisplay,Gxid,Ggc,0,ymax-28,txt,strlen(txt));
    XDrawString(Gdisplay,Gxid,Ggc,i,j-14,"s",1);
  }
  if (Teste(splotar,2)) {
    XSetForeground(Gdisplay,Ggc,cor[3]);
    sprintf(txt,"%7.2f",get_real(tfmax));
    XDrawString(Gdisplay,Gxid,Ggc,0,ymin+26,txt,strlen(txt));
    sprintf(txt,"%7.2f",get_real(tfmin));
    XDrawString(Gdisplay,Gxid,Ggc,0,ymax-14,txt,strlen(txt));
    XDrawString(Gdisplay,Gxid,Ggc,i,j,"dg",2);
  }
  XSetForeground(Gdisplay,Ggc,cor[1]);
  sprintf(txt,"%7.2f",get_real(tgmax));
  XDrawString(Gdisplay,Gxid,Ggc,0,ymin+12,txt,strlen(txt));
  sprintf(txt,"%7.2f",get_real(tgmin));
  XDrawString(Gdisplay,Gxid,Ggc,0,ymax,txt,strlen(txt));
  XDrawString(Gdisplay,Gxid,Ggc,i,j+14,"dB",2);
  XSetForeground(Gdisplay,Ggc,cor[0]);
  XFillRectangle(Gdisplay,Gxid,Ggc,0,ymax+1,
    get_dx(cfrequencia),get_dy(cfrequencia)-ymax-1);
  XSetForeground(Gdisplay,Ggc,cor[1]);
  sprintf(txt,"% .4E",get_real(twmin));
  XDrawString(Gdisplay,Gxid,Ggc,xmin,ymax+12,txt,strlen(txt));
  sprintf(txt,"% .4E",get_real(twmax));
  XDrawString(Gdisplay,Gxid,Ggc,xmax-80,ymax+12,txt,strlen(txt));
  XDrawString(Gdisplay,Gxid,Ggc,(xmax+xmin)/2,
    ymax+12,unid[Rads()],strlen(unid[Rads()]));
}

short Limita(a,b,y)
double a,b,y;
{
  y=a*y+b;
  if (y<ymin)
    return ymin;
  else if (y>ymax)
    return ymax;
  else
    return ((short)floor(y+0.5));
}

double Cdiv(a1,a2,b1,b2)
double a1,a2,b1,b2;
{
  double Result,t;

  if (b1==0 || b2==0) {
    t=1/(b1*b1+b2*b2);
    Result=(a1*b1+a2*b2)*t;
    Imag=(a2*b1-a1*b2)*t;
    return Result;
  }
  t=1/(b1/b2+b2/b1);
  Result=(a1/b2+a2/b1)*t;
  Imag=(a2/b2-a1/b1)*t;
  return Result;
}

notify_canvas(PlotarRespostaEmFrequencia)
{
  short i,j,k;
  double cte;
  fdet *WITH;

  if (!Fpronto) {
    Fdisplay=dpy;
    Fxid=xwin;
    Fgc=DefaultGC(dpy,DefaultScreen(dpy));
    Fpronto=1;
    return;
  }
  WITH=funcao[0];
  if (!(WITH->numerador_valido && WITH->denominador_valido))
    return;
  Gdisplay=Fdisplay; Gxid=Fxid,Ggc=Fgc;
  if (!resposta_plotada)
    ultpt=-1;
  xv_set(jfrequencia,XV_LABEL,"Frequency Response",NULL);
  xmin=60;
  xmax=get_dx(cfrequencia)-4;
  ymin=1;
  ymax=get_dy(cfrequencia)-15;
  xq=xmin+8;
  yq=ymax-70;
  if (get_real(twmin)<=0 || get_real(twmax)<=0)
    set_sel(slog,1);
  if (Log()) {
    dx=Ex(get_real(twmax)/get_real(twmin),
	    1.0/get_int(tsegmentos));
    aw=(xmax-xmin)/log(get_real(twmax)/get_real(twmin));
    bw=xmax-aw*log(get_real(twmax));
  } else {
    dx=(get_real(twmax)-get_real(twmin))/get_int(tsegmentos);
    aw=(xmax-xmin)/(get_real(twmax)-get_real(twmin));
    bw=xmax-aw*get_real(twmax);
  }
  ah=(double)(xmax-xmin)/get_int(tsegmentos);
  bh=xmin;
  csr=0;
  ag=(ymax-ymin)/(get_real(tgmin)-get_real(tgmax));
  bg=ymax-ag*get_real(tgmin);
  af=(ymax-ymin)/(get_real(tfmin)-get_real(tfmax));
  bf=ymax-af*get_real(tfmin);
  at=(ymax-ymin)/(get_real(tamin)-get_real(tamax));
  bt=ymax-at*get_real(tamin);
  if (get_real(twmax)<get_real(twmin) || get_real(tgmax)<get_real(tgmin))
    set_sel(splotar,get_sel(splotar)&~0);
  XSetForeground(Gdisplay,Ggc,cor[0]);
  XFillRectangle(Gdisplay,Gxid,Ggc,0,0,get_dx(cfrequencia),get_dy(cfrequencia));
  if (Teste(splotar,1)) {
    XSetLineAttributes(Gdisplay,Ggc,0,LineOnOffDash,CapButt,JoinMiter);
    XSetForeground(Gdisplay,Ggc,cor[cor_fraca]);
    if (get_real(twmax)-get_real(twmin) >
	get_real(twmin) && Log())
      t1=get_real(twmin);
    else
      t1=get_real(twmax)-get_real(twmin);
    t1=Ex(10.0,(double)((long)floor(log(t1)/log(10.0)-0.499999+0.5)));
    t2=(long)floor(get_real(twmin)/t1+1)*t1;
    while (t2<get_real(twmax)) {
      if (!Log()) {
	i=(long)floor(aw*t2+bw+0.5);
	XDrawLine(Gdisplay,Gxid,Ggc,i,ymin,i,ymax);
	t2+=t1;
	continue;
      }
      if ((long)floor(t2/t1+0.5)==10) {
	t1=10*t1;
	XSetForeground(Gdisplay,Ggc,cor[2]);
      }
      i=(long)floor(aw*log(t2)+bw+0.5);
      XDrawLine(Gdisplay,Gxid,Ggc,i,ymin,i,ymax);
      t2+=t1;
      XSetForeground(Gdisplay,Ggc,cor[cor_fraca]);
    }
    t1=get_real(tgmax)-get_real(tgmin);
    t1=Ex(10.0,(double)((long)floor(log(t1)/log(10.0))));
    t2=(long)floor(get_real(tgmin)/t1+1)*t1;
    while (t2<get_real(tgmax)) {
      i=Limita(ag,bg,t2);
      XDrawLine(Gdisplay,Gxid,Ggc,xmin,i,xmax,i);
      t2+=t1;
    }
  }
  XSetLineAttributes(Gdisplay,Ggc,0,LineSolid,CapButt,JoinMiter);
  XSetForeground(Gdisplay,Ggc,cor[1]);
  XDrawRectangle(Gdisplay,Gxid,Ggc,xmin,ymin,xmax-xmin,ymax-ymin);
  ResetSprite(0);
  TracarEscalas();
  f=get_real(twmin);
  ix=0;
  do {
    if (ix>ultpt) {
      for (i=0; i<=nref; i++) {
	WITH=funcao[i];
	cte=WITH->cten/WITH->cted;
	if (Normalizar())
	  fatord=1.0;
	else
	  fatord=WITH->fator;
	if (Rads())
	  w=f/fatord;
	else
	  w=DoisPi*f/fatord;
	b1=0.0;
	b2=0.0;
	db1=0.0;
	db2=0.0;
	for (j=WITH->dgrau; j>=0; j--) {
	  t=b1*w;
	  b1=WITH->Den[j]-w*b2;
	  b2=t;
	}
	for (j=WITH->dgrau; j>=1; j--) {
	  t=db1*w;
	  db1=j*WITH->Den[j]-w*db2;
	  db2=t;
	}
	a1=0.0;
	a2=0.0;
	da1=0.0;
	da2=0.0;
	for (j=WITH->ngrau; j>=0; j--) {
	  t=a1*w;
	  a1=WITH->Num[j]-w*a2;
	  a2=t;
	}
	for (j=WITH->ngrau; j>=1; j--) {
	  t=da1*w;
	  da1=j*WITH->Num[j]-w*da2;
	  da2=t;
	}
	sr=cte*Cdiv(a1,a2,b1,b2);
	si=cte*Imag;
	if (sr==0) {
	  if (si==0)
	    si=1e-11;
	  sr=si;
	}
	WITH->Fas[ix]=atan(si/sr)*RadGraus;
	WITH->Gan[ix]=log(sr*sr+si*si)*LnDb;
	WITH->Tg[ix]=(Cdiv(db1,db2,b1,b2)-Cdiv(da1,da2,a1,a2))/fatord;
	if (sr<0) {
	  if (si>0)
	    WITH->Fas[ix]=180+WITH->Fas[ix];
	  else
	    WITH->Fas[ix]-=180;
	}
      }
      Frq[ix]=f;
    }
    j=(long)floor(ix*ah+bh+0.5);
    for (i=nref; i>=0; i--) {
      WITH=funcao[i];
      if (modo1)
	XSetForeground(Gdisplay,Ggc,cor[1]);
      else
	XSetForeground(Gdisplay,Ggc,cor[i%MAXCOR+1]);
      k=Limita(ag,bg,WITH->Gan[ix]);
      if (ix>0)
	XDrawLine(Gdisplay,Gxid,Ggc,xa,WITH->ga,j,k);
      WITH->ga=k;
      if (Teste(splotar,2)) {
	if (modo1)
	  XSetForeground(Gdisplay,Ggc,cor[3]);
	else
	  XSetForeground(Gdisplay,Ggc,cor[i%MAXCOR+1]);
	k=Limita(af,bf,WITH->Fas[ix]);
	if (ix>0)
	  XDrawLine(Gdisplay,Gxid,Ggc,xa,WITH->fa,j,k);
	WITH->fa=k;
      }
      if (Teste(splotar,4)) {
	if (modo1)
	  XSetForeground(Gdisplay,Ggc,cor[2]);
	else
	  XSetForeground(Gdisplay,Ggc,cor[i%MAXCOR+1]);
	k=Limita(at,bt,WITH->Tg[ix]);
	if (ix>0)
	  XDrawLine(Gdisplay,Gxid,Ggc,xa,WITH->ta,j,k);
	WITH->ta=k;
      }
    }
    xa=j;
    if (Log())
      f*=dx;
    else
      f+=dx;
    ix++;
  } while (ix<=get_int(tsegmentos));
  ix=get_int(tsegmentos);
  ultpt=ix;
  resposta_plotada=true;
}

 
void PutCursor(void)
{
  fdet *WITH;
  char STR1[256];
  char STR3[256];

  WITH=funcao[atual];
  PutSprite((long)floor(ah*csr+bh+0.5),Limita(ag,bg,WITH->Gan[csr]),0);
  XSetForeground(Gdisplay,Ggc,cor[0]);
  XFillRectangle(Gdisplay,Gxid,Ggc,xq,yq,120,65);
  XSetForeground(Gdisplay,Ggc,cor[2]);
  XDrawRectangle(Gdisplay,Gxid,Ggc,xq-1,yq-1,121,66);
  XSetForeground(Gdisplay,Ggc,cor[1]);
  XDrawString(Gdisplay,Gxid,Ggc,xq+2,yq+12,NomeAtual(STR1,atual),strlen(STR1));
  sprintf(STR3,"%12g %s",Frq[csr],unid[Rads()]);
  XDrawString(Gdisplay,Gxid,Ggc,xq,yq+24,STR3,strlen(STR3));
  sprintf(STR3,"%13.8f dB",WITH->Gan[csr]);
  XDrawString(Gdisplay,Gxid,Ggc,xq,yq+36,STR3,strlen(STR3));
  sprintf(STR3,"%13.8f dg",WITH->Fas[csr]);
  XDrawString(Gdisplay,Gxid,Ggc,xq,yq+48,STR3,strlen(STR3));
  sprintf(STR3,"%13.8f s",WITH->Tg[csr]);
  XDrawString(Gdisplay,Gxid,Ggc,xq,yq+60,STR3,strlen(STR3));
}

event_canvas(EventosResposta)
{
  static short xi=0,yi=0,xf=0,yf=0;
  static boolean selecao=false;
  double TEMP;
  int evento;

  if (!Fpronto) return;
  if (!resposta_plotada) return;
  Gdisplay=Fdisplay; Gxid=Fxid; Ggc=Fgc;
  if (selecao) {
    XSetFunction(Gdisplay,Ggc,GXxor); 
    XSetForeground(Gdisplay,Ggc,c_cursor);
    if (event_id(event)==LOC_DRAG) {
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      xf=event_x(event);
      yf=event_y(event);
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      return;
    }
    else {
      selecao=false;
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      XSetFunction(Gdisplay,Ggc,GXcopy);
      if (xi>=xf || yi>=yf) return;
      resposta_plotada=false;
      set_real(twmin,(xi-bw)/aw);
      if (Log())
	set_real(twmin,exp(get_real(twmin)));
      set_real(twmax,(xf-bw)/aw);
      if (Log())
	set_real(twmax,exp(get_real(twmax)));
      set_real(tgmin,(yf-bg)/ag);
      set_real(tgmax,(yi-bg)/ag);
    }
    goto Recalcular;
  }
  evento=event_id(event);
  if ((evento>='a') && (evento<='z')) evento=toupper(evento);
  switch (evento) {

  /* As cores ficam erradas e o botao esquerdo nao funciona */
  /*
  case MS_RIGHT:
    menu_show(menu1,window,event,NULL);
    return;
  */

  case MS_LEFT:
    xi=event_x(event);
    yi=event_y(event);
    xf=xi;
    yf=yi;
    selecao=true;
    return;

  case MS_MIDDLE:
  case LOC_DRAG:
    csr=(int)((event_x(event)-bh)/ah+0.5);
    if (csr<0) csr=0;
    if (csr>ix) csr=ix;
    PutCursor();
    return;

  case KLEFTARROW:
    if (csr>=1) csr--;
    PutCursor();
    return;

  case KPAGEDOWN:
    if (csr>=10) csr-=10;
    PutCursor();
    return;

  case KRIGHTARROW:
    if (csr<ix) csr++;
    PutCursor();
    return;

  case KPAGEUP:
    if (csr<=ix-10) csr+=10;
    PutCursor();
    return;

  case KUPARROW:
    t=(get_real(tgmax)-get_real(tgmin))/2;
    set_real(tgmin,get_real(tgmin)+t);
    set_real(tgmax,get_real(tgmax)+t);
    break;

  case KDOWNARROW:
    t=(get_real(tgmax)-get_real(tgmin))/2;
    set_real(tgmin,get_real(tgmin)-t);
    set_real(tgmax,get_real(tgmax)-t);
    break;

  case '-':
    set_real(tgmax,2*get_real(tgmax)-get_real(tgmin));
    break;

  case '+':
    set_real(tgmax,(get_real(tgmax)+get_real(tgmin))/2);
    break;

  case '\t':
    if (atual<nref) atual++;
    else atual=0;
    PutCursor();
    return;

  case '\b':
    if (atual>0) atual--;
    else atual=nref;
    PutCursor();
    return;

  case 'G':
    Inverter(splotar,1);
    break;

  case 'F':
    Inverter(splotar,2);
    break;

  case 'T':
    Inverter(splotar,4);
    break;

  case 'L':
    if (Log()) set_sel(slog,1);
    else set_sel(slog,0);
    resposta_plotada=false;
    break;

  case 'R':
    if (Log()) {
      TEMP=get_real(twmax)/get_real(twmin);
      set_real(twmax,get_real(twmin)*TEMP*TEMP);
    }
    else set_real(twmax,get_real(twmin)+(get_real(twmax)-get_real(twmin))*2);
    resposta_plotada=false;
    break;

  case 'A':
    if (Log()) 
      set_real(twmax,get_real(twmin)*sqrt(get_real(twmax)/get_real(twmin)));
    else
      set_real(twmax,get_real(twmin)+(get_real(twmax)-get_real(twmin))/2);
    resposta_plotada=false;
    break;

  case '>':
  case '.':
    if (Log()) {
      t=sqrt(sqrt(get_real(twmax)/get_real(twmin)));
      set_real(twmin,get_real(twmin)*t);
      set_real(twmax,get_real(twmax)*t);
    } else {
      t=(get_real(twmax)-get_real(twmin))/4;
      set_real(twmin,get_real(twmin)+t);
      set_real(twmax,get_real(twmax)+t);
    }
    resposta_plotada=false;
    break;

  case '<':
  case ',':
    if (Log()) {
      t=sqrt(sqrt(get_real(twmax)/get_real(twmin)));
      set_real(twmin,get_real(twmin)/t);
      set_real(twmax,get_real(twmax)/t);
    } else {
      t=(get_real(twmax)-get_real(twmin))/4;
      set_real(twmin,get_real(twmin)-t);
      set_real(twmax,get_real(twmax)-t);
    }
    resposta_plotada=false;
    break;

  case 'C':
    modo1=!modo1;
    break;

  case 'Z':
    ZoomOut();
    resposta_plotada=false;
    break;

  default:
    /* if (evento!=LOC_MOVE) printf("Evento: %d\n",evento); */
    return;
  }
 Recalcular: 
  PlotarRespostaEmFrequencia(cfrequencia,NULL,Fdisplay,Fxid,NULL);
}

short LimX(x)
double x;
{
  double t;

  t=ax*x+bx;
  if (t>xpmax)
    return xpmax;
  else if (t<0)
    return 0;
  else
    return ((long)floor(t+0.5));
}

short LimY(y)
double y;
{
  t=ay*y+by;
  if (t>ypmax)
    return ypmax;
  else if (t<0)
    return 0;
  else
    return ((long)floor(t+0.5));
}

void Plotar(grau,Re,Im,polo)
short grau;
double *Re,*Im;
boolean polo;
{
  short i,x,y;

  for (i=0; i<grau; i++) {
    x=LimX(Re[i]*fatord);
    y=LimY(Im[i]*fatord);
    if (polo) {
      XDrawLine(Gdisplay,Gxid,Ggc,x-2,y-2,x+2,y+2);
      XDrawLine(Gdisplay,Gxid,Ggc,x-2,y+2,x+2,y-2);
    } else
      XDrawArc(Gdisplay,Gxid,Ggc,x-4,y-4,8,8,0,360*64);
  }
}

notify_canvas(PlotarPolosEZeros)
{
  short i;
  fdet *WITH;
 
  if (!Rpronto) {
    Rdisplay=dpy;
    Rxid=xwin;
    Rgc=DefaultGC(dpy,DefaultScreen(dpy));
    Rpronto=1;
    return;
  }
  WITH=funcao[atual];
  if (!(WITH->zeros_validos || WITH->polos_validos)) return;
  Gdisplay=Rdisplay; Gxid=Rxid,Ggc=Rgc;
  ResetSprite(1);
  XSetForeground(Gdisplay,Ggc,cor[0]);
  XFillRectangle(Gdisplay,Gxid,Ggc,0,0,get_dx(craizes),get_dy(craizes));
  ypmax=get_dy(craizes)-15;
  xpmax=ypmax;
  basex=xpmax+2;
  basey=24;
  ay=-(ypmax/delta);
  by=ypmax-ay*immin;
  ax=xpmax/delta;
  bx=-ax*remin;
  XSetLineAttributes(Gdisplay,Ggc,0,LineOnOffDash,CapButt,JoinMiter);
  XSetForeground(Gdisplay,Ggc,cor[cor_fraca]);
  i=LimX(0.0);
  XDrawLine(Gdisplay,Gxid,Ggc,i,0,i,ypmax);
  i=LimY(0.0);
  XDrawLine(Gdisplay,Gxid,Ggc,0,i,xpmax,i);
  XSetForeground(Gdisplay,Ggc,cor[1]);
  sprintf(txt,"% .3E",remin);
  XDrawString(Gdisplay,Gxid,Ggc,0,ypmax+12,txt,strlen(txt));
  sprintf(txt,"% .3E",remin+delta);
  XDrawString(Gdisplay,Gxid,Ggc,xpmax-70,ypmax+12,txt,strlen(txt));
  sprintf(txt,"% .3E",immin);
  XDrawString(Gdisplay,Gxid,Ggc,basex,ypmax,txt,strlen(txt));
  sprintf(txt,"% .3E",immin+delta);
  XDrawString(Gdisplay,Gxid,Ggc,basex,12,txt,strlen(txt));
  XSetLineAttributes(Gdisplay,Ggc,0,LineSolid,CapButt,JoinMiter);
  XDrawRectangle(Gdisplay,Gxid,Ggc,0,0,xpmax,ypmax);
  for (i=nref; i>=0; i--) {
    WITH=funcao[i];
    XSetForeground(Gdisplay,Ggc,cor[i%MAXCOR+1]);
    if (Normalizar())
      fatord=1.0;
    else
      fatord=WITH->fator;
    if (WITH->polos_validos)
      Plotar(WITH->dgrau,WITH->RePolos,WITH->ImPolos,true);
    if (WITH->zeros_validos)
      Plotar(WITH->ngrau,WITH->ReZeros,WITH->ImZeros,false);
  }
  raizes_plotadas=true;
}

notify_button(AbrirPolosEZeros)
{
  
}

/* Local variables for EventosPolosEZeros: */
struct LOC_EventosPolosEZeros {

  double x,y,x1,y1,dist;
} ;

void Testar(i,n,Re,Im,saopolos,LINK)
short i,n;
double *Re,*Im;
boolean saopolos;
struct LOC_EventosPolosEZeros *LINK;
{
  double teste;
  short j;

  for (j=0; j<n; j++) {
    teste=fabs(LINK->x1-Re[j]*fatord)+fabs(LINK->y1-Im[j]*fatord);
    if (teste<LINK->dist) {
      atual=i;
      LINK->dist=teste;
      polos=saopolos;
      LINK->x=Re[j]*fatord;
      LINK->y=Im[j]*fatord;
    }
  }
}

event_canvas(EventosPolosEZeros)
{
  struct LOC_EventosPolosEZeros V;
  static short xi=0,yi=0,xf=0,yf=0;
  static boolean selecao=false;
  short i;
  fdet *WITH;
  char STR1[256];
  char STR2[256];
  
  if (!Rpronto) return;
  if (!(funcao[0]->polos_validos || funcao[0]->zeros_validos)) return;
  if (!raizes_plotadas) return;
  Gdisplay=Rdisplay; Gxid=Rxid; Ggc=Rgc;
  if (selecao) {
    XSetFunction(Gdisplay,Ggc,GXxor); 
    XSetForeground(Gdisplay,Ggc,c_cursor);
    if (event_id(event)==LOC_DRAG) {
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      yf=event_y(event);
      xf=xi+(long)floor((yi-yf)*ax/ay+0.5);
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      return;
    }
    else {
      selecao=false;
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      XSetFunction(Gdisplay,Ggc,GXcopy);
      if (xi>=xf || yi>=yf)
	return;
      remin=(xi-bx)/ax;
      immin=(yf-by)/ay;
      delta=(yi-yf)/ay;
      goto Replotar;
    }
  }
  switch (event_id(event)) {
    
    case MS_LEFT:
      xi=event_x(event);
      yi=event_y(event);
      xf=xi;
      yf=yi;
      selecao=true;
      return;

    case KUPARROW:
      immin+=delta/4;
      break;

    case KDOWNARROW:
      immin-=delta/4;
      break;

    case KRIGHTARROW:
      remin+=delta/4;
      break;

    case KLEFTARROW:
      remin-=delta/4;
      break;

    case '-':
      immin-=delta/2;
      remin-=delta/2;
      delta*=2;
      break;

    case '+':
      immin+=delta/4;
      remin+=delta/4;
      delta /= 2;
      break;
    
    case LOC_DRAG:
    case MS_MIDDLE:
      V.x1=(event_x(event)-bx)/ax;
      V.y1=(event_y(event)-by)/ay;
      V.dist=1e38;
      for (i=0; i<=nref; i++) {
        WITH=funcao[i];
        if (Normalizar())
	  fatord=1.0;
        else
	  fatord=WITH->fator;
        if (WITH->polos_validos)
	  Testar(i,WITH->dgrau,WITH->RePolos,WITH->ImPolos,true,&V);
        if (WITH->zeros_validos)
	  Testar(i,WITH->ngrau,WITH->ReZeros,WITH->ImZeros,false,&V);
      }
      PutSprite(LimX(V.x),LimY(V.y),1);
      XSetForeground(Gdisplay,Ggc,cor[0]);
      XFillRectangle(Gdisplay,Gxid,Ggc,basex,basey,get_dx(craizes)-basex,72);
      XSetForeground(Gdisplay,Ggc,cor[1]);
      XDrawString(Gdisplay,Gxid,Ggc,basex,basey+12,
        NomeAtual(STR1,atual),strlen(STR1));
      if (polos)
        XDrawString(Gdisplay,Gxid,Ggc,basex,basey+24,"Pole: ",6);
      else
        XDrawString(Gdisplay,Gxid,Ggc,basex,basey+24,"Zero: ",6);
      sprintf(STR2,"Re:%12f",V.x);
      XDrawString(Gdisplay,Gxid,Ggc,basex,basey+36,STR2,strlen(STR2));
      sprintf(STR2,"Im:%12f",V.y);
      XDrawString(Gdisplay,Gxid,Ggc,basex,basey+48,STR2,strlen(STR2));
      w=sqrt(V.x*V.x+V.y*V.y);
      sprintf(STR2,"w: %12f",w);
      XDrawString(Gdisplay,Gxid,Ggc,basex,basey+60,STR2,strlen(STR2));
      if (fabs(V.x)>get_real(tminimo))
        sprintf(STR2,"Q: %12f",-0.5*w/V.x);
      else
        strcpy(STR2,"Q: infinite");
      XDrawString(Gdisplay,Gxid,Ggc,basex,basey+72,STR2,strlen(STR2));
      return;

   default: return;
   }
  Replotar:
   PlotarPolosEZeros(craizes,NULL,Rdisplay,Rxid,NULL);
}

notify_textfield(ZerarGrafico)
{
  resposta_plotada=false;
  return PANEL_NEXT;
}

notify_button(IniciarResposta)
{
  fdet *WITH;

  WITH=funcao[0];
  if (!(WITH->denominador_valido && WITH->numerador_valido)) {
    puts("* No response computed");
    return;
  }
  wmin0=get_real(twmin);
  wmax0=get_real(twmax);
  gmin0=get_real(tgmin);
  gmax0=get_real(tgmax);
  open_window(jfrequencia);
  PlotarRespostaEmFrequencia(cfrequencia,NULL,Fdisplay,Fxid,NULL);
  if (get_sel(sraizes)==0) {
    open_window(jraizes);
    InicializaRaizes();
    PlotarPolosEZeros(craizes,NULL,Rdisplay,Rxid,NULL);
  }
}

notify_textfield(SetarNome)
{
  char STR1[50];

  strcpy(txt,get_text(ttitulo));
  iii=get_int(tnsaida);
  sprintf(STR1,"%s.n%d",txt,iii);
  xv_set(tnumerador,PANEL_VALUE,STR1,NULL);
  sprintf(STR1,"%s.d",txt);
  xv_set(tdenominador,PANEL_VALUE,STR1,NULL);
  sprintf(STR1,"%s.z%d",txt,iii);
  xv_set(tzeros,PANEL_VALUE,STR1,NULL);
  sprintf(STR1,"%s.r",txt);
  xv_set(tpolos,PANEL_VALUE,STR1,NULL);
  return PANEL_NEXT;
}

notify_button(LerReferencia)
{
  fdet *WITH;

  if (!AlocarReferencia())
    return;
  WITH=funcao[nref];
  strcpy(WITH->nome,get_text(tnumerador));
  WITH->numerador_valido=LerPolinomio(WITH->nome,&WITH->ngrau,&WITH->cten,
					&WITH->fator,WITH->Num);
  WITH->denominador_valido=LerPolinomio(get_text(tdenominador),
      &WITH->dgrau,&WITH->cted,&WITH->fator,WITH->Den);
  WITH->zeros_validos=LerRaizes(get_text(tzeros),&WITH->ngrau,
      &WITH->cten,&WITH->fator,WITH->ReZeros,WITH->ImZeros);
  WITH->polos_validos=LerRaizes(get_text(tpolos),&WITH->dgrau,
      &WITH->cted,&WITH->fator,WITH->RePolos,WITH->ImPolos);
  if (!(WITH->numerador_valido && WITH->denominador_valido)) {
    puts("* Reference incomplete");
    DesalocarReferencia();
    return;
  }
  atual=nref;
  resposta_plotada=false;
  raizes_plotadas=false;
  close_window(jreferencia);
}

notify_menu(TratarMenu1)
{
  short i,FORLIM;
  char STR3[256];
  fdet *WITH;

  switch (get_item(obj)) {

  case 1:
    open_window(jdiretorio);
    break;

  case 2:
    PrepararAnalise();
    break;

  case 3:
    open_window(jpfrequencia);
    break;

  case 4:
    FORLIM=nref;
    for (atual=0; atual<=FORLIM; atual++) CalcularPolosEZeros();
    atual=0;
    open_window(jraizes);
    InicializaRaizes();
    PlotarPolosEZeros(craizes,NULL,Rdisplay,Rxid,NULL);
    break;

  case 5:
    if (netlist_lido)
      xv_set(jedit,XV_SHOW,TRUE,FRAME_CMD_PUSHPIN_IN,TRUE,NULL);
    else
      puts("* No netlist read");
    break;

  case 6:
    printf("IFFT - Version %s\n",versao);
    puts("Linear circuit analysis with FFT interpolation");
    puts("By: Antonio Carlos Moreirao de Queiroz");
    puts("COPPE-DEEL");
    puts("Universidade Federal do Rio de Janeiro-1992");
    puts("e-mail: acmq@coe.ufrj.br");
    puts("Stored transfer functions: ");
    FORLIM=nref;
    for (i=0; i<=FORLIM; i++) {
      WITH=funcao[i];
      printf("%s (",NomeAtual(STR3,i));
      if (WITH->denominador_valido)
	printf(" den. ");
      if (WITH->numerador_valido)
	printf(" num. ");
      if (WITH->polos_validos)
	printf(" poles ");
      if (WITH->zeros_validos)
	printf(" zeros ");
      puts(")");
    }
    break;

  case 7:
    open_window(jextra);
    break;

  case 8:
    if (netlist_lido)
      open_window(jmontecarlo);
    else
      puts("* No netlist read");
    break;

  case 9:
    puts("IFFT terminated");
    notify_stop();
  }
}

notify_menu(TratarMenu2)
{
  short i;
  time_t t;
  char STR1[256],STR2[256],STR3[256];

  switch (get_item(obj)) {

  case 1:
    if (resposta_plotada) {
      sprintf(txt,"%s.g%d",rede,get_int(tsaida));
      arquivo=fopen(txt,"w");
      time(&t);
      fprintf(arquivo,"IFFT - %sNetwork: %s; Frequency response; Output %d\n",ctime(&t),rede,get_int(tsaida));
      sprintf(STR1,"Freq. (%s)",unid[Rads()]);
      fprintf(arquivo,"%14s %14s %14s %14s\n",STR1,"Gain (dB)","Phase (def)","Delay (s)");
      for (i=0; i<=ultpt; i++)
	fprintf(arquivo,"%14.9f %14.9f %14.9f %14.9f\n",Frq[i],funcao[0]->Gan[i],funcao[0]->Fas[i],funcao[0]->Tg[i]);
      putc('\n',arquivo);
      fclose(arquivo);
      printf("Table saved in file %s\n",txt);
    } else
      puts("* No response computed");
    break;

  case 2:
    if (funcao[0]->denominador_valido) {
      sprintf(STR2,"%s.d",rede);
      SalvarPolinomio(STR2,funcao[0]->dgrau,funcao[0]->cted,funcao[0]->fator,funcao[0]->Den);
    } else
      puts("* No denominator computed");
    if (funcao[0]->numerador_valido) {
      sprintf(STR1,"%s.n%d",rede,get_int(tsaida));
      SalvarPolinomio(STR1,funcao[0]->ngrau,funcao[0]->cten,funcao[0]->fator,funcao[0]->Num);
    } else
      puts("* No numerator computed");
    break;

  case 3:
    if (funcao[0]->polos_validos) {
      sprintf(STR3,"%s.r",rede);
      SalvarRaizes(STR3,funcao[0]->dgrau,funcao[0]->cted,funcao[0]->fator,funcao[0]->RePolos,funcao[0]->ImPolos);
    } else
      puts("* No poles computed");
    if (funcao[0]->zeros_validos) {
      sprintf(STR2,"%s.z%d",rede,get_int(tsaida));
      SalvarRaizes(STR2,funcao[0]->ngrau,funcao[0]->cten,funcao[0]->fator,funcao[0]->ReZeros,funcao[0]->ImZeros);
    } else
      puts("* No zeros computed");
    break;
  }
}

notify_menu(TratarMenu3)
{
  short i,j,n;
  char STR1[256];
  char STR3[256];
  short FORLIM1;
  fdet *WITH;

  switch (get_item(obj)) {

  case 1:
    if (funcao[0]->denominador_valido || funcao[0]->numerador_valido ||
	funcao[0]->polos_validos || funcao[0]->zeros_validos) {
      if (AlocarReferencia())
	*funcao[nref]=*funcao[0];
    } else
      puts("* No function computed/read");
    break;

  case 2:
    DesalocarReferencia();
    break;

  case 3:
    if (nref>0) {
      while (nref>0)
	DesalocarReferencia();
    } else
      puts("* No references stored");
    break;

  case 4:
    open_window(jreferencia);
    break;

  case 5:
    *funcao[0]=*funcao[nref];
    printf("Reference #%d restored\n",nref);
    sprintf(rede,"Ref%d",nref);
    DesalocarReferencia();
    break;

  case 6:
    if (nref>0) {
      if (resposta_plotada) {
	sprintf(STR1,"%s.rfr",rede);
 	arquivo=fopen(STR1,"w");
	for (j=1; j<=nref; j++) {
          WITH=funcao[j]; 
	  fprintf(arquivo,"# Frequency response - Ref #%d\n",j);
	  for (i=0; i<=ultpt; i++)
	    fprintf(arquivo,"%14.9f %14.9f %14.9f %14.9f\n",
		    Frq[i],WITH->Gan[i],WITH->Fas[i],WITH->Tg[i]);
	  putc('\n',arquivo);
	}
	fclose(arquivo);
	printf("%d responses saved in file %s.rfr\n",
		nref,rede);
      }
      sprintf(STR3,"%s.rpo",rede);
      arquivo=fopen(STR3,"w");
      n=0;
      for (j=1; j<=nref; j++) {
	WITH=funcao[j];
	if (WITH->polos_validos) {
	  fprintf(arquivo,"Poles - Ref #%d\n",j);
	  FORLIM1=WITH->dgrau;
	  for (i=0; i<FORLIM1; i++)
	    fprintf(arquivo,"% .5E % .5E\n",
		    WITH->fator*WITH->RePolos[i],
		    WITH->fator*WITH->ImPolos[i]);
	  putc('\n',arquivo);
	  n++;
	}
      }
      fclose(arquivo);
      printf("%d groups of poles saved in file %s.rpo\n",n,rede);
      sprintf(STR1,"%s.rze",rede);
      arquivo=fopen(STR1,"w");
      n=0;
      for (j=1; j<=nref; j++) {
	WITH=funcao[j];
	if (WITH->zeros_validos) {
	  fprintf(arquivo,"Zeros - Ref #%d\n",j);
	  FORLIM1=WITH->ngrau;
	  for (i=0; i<FORLIM1; i++)
	    fprintf(arquivo,"% .5E % .5E\n",
		    WITH->fator*WITH->ReZeros[i],
		    WITH->fator*WITH->ImZeros[i]);
	  putc('\n',arquivo);
	  n++;
	}
      }
      fclose(arquivo);
      printf("%d groups of zeros saved in file %s.rze\n",n,rede);
    }
    break;
  }
}

notify_button(ExecutarVarredura)
{
  short esweep,psweep;
  double vmin,vmax,vsweep,voriginal,vstep;
  boolean lin;
  elemento *WITH;
  _REC_biblioteca *WITH1;

  esweep=1;
  while (esweep<=numero &&
	 strcmp(netlist[esweep-1].nome,get_text(tswel)))
    esweep++;
  if (esweep>numero) {
    printf("* Element %s not found\n",get_text(tswel));
    return;
  }
  WITH=&netlist[esweep-1];
  WITH1=&biblioteca[(long)WITH->tipo];
  if (get_int(tswval)>WITH1->nval) {
    printf("* The element %s has only %d value(s)\n",
	    get_text(tswel),WITH1->nval);
    return;
  }
  voriginal=netlist[esweep-1].val[get_int(tswval)-1];
  while (nref>0)
    DesalocarReferencia();
  while (AlocarReferencia() && nref<get_int(tswn)) ;
  printf("Sweeping %s (%s):\n",
	  get_text(tswel),
	  WITH1->nmval[get_int(tswval)-1]);
  if (get_sel(ssweep)==0) {
    vmin=get_real(tswmin);
    vmax=get_real(tswmax);
    vstep=(get_real(tswmax)-vsweep)/(nref-1);
  } else {
    vmin=get_real(tswmin)/100*voriginal;
    vmax=get_real(tswmax)/100*voriginal;
    vstep=(get_real(tswmax)/100*voriginal-vsweep)/(nref-1);
  }
  lin=(get_sel(sescala)==0 || vmin==0);
  if (lin)
    vstep=(vmax-vmin)/(nref-1);
  else
    vstep=Ex(vmax/vmin,1.0/(nref-1));
  vsweep=vmin;
  for (psweep=1; psweep<=nref; psweep++) {
    printf("%s: %s=%g; Ref #%d\n",
	    WITH->nome,
	    biblioteca[(long)WITH->tipo].nmval[get_int(tswval)-1],
	    vsweep,psweep);
    WITH->val[get_int(tswval)-1]=vsweep;
    InvalidarAnalise(NULL,NULL);
    IniciarAnalise(NULL,NULL);
    *funcao[psweep]=*funcao[0];
    if (lin)
      vsweep+=vstep;
    else
      vsweep*=vstep;
  }
  WITH->val[get_int(tswval)-1]=voriginal;
  analise_feita=false;
  printf("Sweep completed. Results in refs. #1-#%d\n",nref);
  if (nref!=get_int(tswn)) {
    printf("* Memory was enough for only %d functions\n",nref);
  }
}

notify_button(AbrirSweep)
{
  close_window(jsweep);
  xv_set(tswel,PANEL_VALUE,netlist[eedit-1].nome,NULL);
  open_window(jsweep);
}

notify_button(MonteCarlo)
{
  elemento *pnetlist;
  short i,j,k,nrun;
  unsigned short mm;
  double tol,r;
  elemento *WITH;

  close_window(jmontecarlo);
  while (nref>0) DesalocarReferencia();
  mm=numero*sizeof(elemento);
  if ((pnetlist=(elemento *)malloc(mm))==NULL) {
    puts("* Not enough memory");
    return;
  }
  for (i=0; i<numero; i++) pnetlist[i]=netlist[i];
  while (AlocarReferencia() && nref<get_int(tmonten)) ;
  printf("Running Monte Carlo analysis with %d circuits\n",nref);
  srandom();
  for (nrun=1; nrun<=nref; nrun++) {
    for (i=0; i<numero; i++) {
      WITH=&netlist[i];
      k=biblioteca[(long)WITH->tipo].nval;
      for (j=0; j<k; j++) {
	if (WITH->tipo!=FonteV && (WITH->tipo!=FonteF || j+1!=2)) {
	  if (WITH->tipo==Capacitor || WITH->tipo==Indutor ||
	      WITH->tipo==Transformador)
	    tol=get_real(tmontetlcm);
	  else
	    tol=get_real(tmontetr);
	  if (get_sel(sdistribuicao)==0)
	    r=2*RANDOM-1;
	  else
	    r=RandGauss()/3;
	  WITH->val[j]=pnetlist[i].val[j]*(1+tol*r);
	}
      }
    }
    InvalidarAnalise(NULL,NULL);
    IniciarAnalise(NULL,NULL);
    *funcao[nrun]=*funcao[0];
    printf("Circuit #%d completed\n",nrun);
  }
  analise_feita=false;
  printf("Monte Carlo analysis completed.\nResults in refs. #1-#%d\n",nref);
  if (nref!=get_int(tmonten)) {
    printf("* Memory was enough for only %d circuits\n",nref);
  }
  for (i=0; i<numero; i++) netlist[i]=pnetlist[i];
  free(pnetlist);
}
 
void main(int argc,char* argv[])
{
  printf("\nIFFT, Version %s\nBy Antonio Carlos M. de Queiroz\n",versao);
  arquivo=NULL;
  DoisPi=2*M_PI;
  RadGraus=180/M_PI;
  LnDb=10/log(10.0);
  strcpy(rede,"ifft");
  xv_init(XV_INIT_ARGC_PTR_ARGV,&argc,argv,NULL);
  funcao[0]=(fdet *)malloc(sizeof(fdet));
  atual=0;
  InvalidarAnalise(NULL,NULL);
  menu2=xv_create(NULL,MENU,
    MENU_TITLE_ITEM,"Save:",
    MENU_STRINGS,"frequency response","transfer function",
      "poles and zeros",
    NULL,
    MENU_NOTIFY_PROC,TratarMenu2,
  NULL);
  menu3=xv_create(NULL,MENU,
    MENU_TITLE_ITEM,"References:",
    MENU_STRINGS,"store last results","delete last reference",
      "delete all references","read reference","restore last reference",
      "save all references",
    NULL,
    MENU_NOTIFY_PROC,TratarMenu3,
  NULL);
  menu1=xv_create(NULL,MENU,
    MENU_TITLE_ITEM,"Options:",
    MENU_STRINGS,"netlist","analysis","frequency response",
      "poles and zeros","edit","informations",
      "roots parameters","Monte Carlo","quit",
    NULL,
    MENU_PULLRIGHT_ITEM,"references",menu3,
    MENU_PULLRIGHT_ITEM,"save",menu2,
    MENU_NOTIFY_PROC,TratarMenu1,
  NULL);

  jfrequencia=xv_create(NULL,FRAME,
    XV_WIDTH,640,
    XV_HEIGHT,480,
    XV_X,0,
    XV_Y,0,
    XV_LABEL,"IFFT",
    NULL);
  closed_image=(Server_image)xv_create(NULL,SERVER_IMAGE,
    XV_WIDTH,64,
    XV_HEIGHT,64,
    SERVER_IMAGE_BITS,closed_bits,
    NULL);
  icon=(Icon)xv_create(jfrequencia,ICON,
    ICON_IMAGE,closed_image,
    XV_X,100,
    XV_Y,100,
    NULL);
  xv_set(jfrequencia,FRAME_ICON,icon,NULL);  

  {Display *dpy=(Display*)xv_get(jfrequencia,XV_DISPLAY); 
    if (DefaultDepth(dpy,DefaultScreen(dpy))>1)
      cms=xv_create(NULL,CMS,
        CMS_TYPE,XV_STATIC_CMS,
        CMS_SIZE,7,
        CMS_NAMED_COLORS,"black","white","yellow","red","green","orange","gray",NULL,
        NULL);
    else {
      printf("Black and white mode\n");
      cms=xv_create(NULL,CMS,
        CMS_SIZE,7,
        CMS_TYPE,XV_STATIC_CMS,
        CMS_NAMED_COLORS,"black","white","white","white","white","white","white",NULL,
        NULL);
    }
    cor=(unsigned long *)xv_get(cms,CMS_INDEX_TABLE);
  }
  if (cms==NULL) printf("Problems in colormap segment creation\n");
  c_cursor=cor[0]^cor[5];
 
  panel=(Panel)xv_create(jfrequencia,PANEL,
    XV_X,0,
    XV_Y,0,
    XV_WIDTH,WIN_EXTEND_TO_EDGE,
    XV_HEIGHT,30,
    PANEL_LAYOUT,PANEL_HORIZONTAL,
    NULL);
  xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Menu",
    PANEL_ITEM_MENU,menu1,
    NULL);
  cfrequencia=xv_create(jfrequencia,CANVAS,
    WIN_CMS,cms,
    XV_X,0,
    XV_Y,30,
    CANVAS_X_PAINT_WINDOW,TRUE,
    CANVAS_REPAINT_PROC,PlotarRespostaEmFrequencia,
    NULL);

  xv_set(canvas_paint_window(cfrequencia),
    WIN_EVENT_PROC,EventosResposta,
    WIN_CONSUME_EVENTS,
      WIN_ASCII_EVENTS,LOC_DRAG,LOC_MOVE,WIN_MOUSE_BUTTONS,
      WIN_TOP_KEYS,WIN_META_EVENTS,
      NULL,
    WIN_IGNORE_EVENTS,WIN_UP_EVENTS,WIN_UP_ASCII_EVENTS,
      NULL,
    NULL);

  jextra=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"Roots Calculation Parameters",
    XV_X,6,
    XV_Y,57,
    NULL);
  panel=(Panel)xv_get(jextra,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  ttol=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
   
    PANEL_LABEL_STRING,"Root tolerance",
    PANEL_VALUE,"1e-11",
    PANEL_NOTIFY_PROC,InvalidarRaizes,
    NULL);
  ttolm=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Derivative tolerance",
    PANEL_VALUE,"1e-11",
    PANEL_NOTIFY_PROC,InvalidarRaizes,
    NULL);
  treal=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Real approximation",
    PANEL_VALUE,"1.1",
    PANEL_NOTIFY_PROC,InvalidarRaizes,
    NULL);
  timag=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Imag approximation",
    PANEL_VALUE,"1.1",
    PANEL_NOTIFY_PROC,InvalidarRaizes,
    NULL);
  tminimo=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Minimum non zero value",
    PANEL_VALUE,"1e-8",
    PANEL_NOTIFY_PROC,InvalidarRaizes,
    NULL);
  smetodo=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Method",
    PANEL_CHOICE_STRINGS,"Bairstow","Newton-Raphson",NULL,
    PANEL_VALUE,1,
    PANEL_NOTIFY_PROC,InvalidarRaizes,
    NULL);
  window_fit(panel);
  window_fit(jextra);

  jparametros=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"Analysis Parameters",
    XV_X,6,
    XV_Y,57,
    NULL);
  panel=(Panel)xv_get(jparametros,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  tfatorw=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Frequency normalization factor",
    PANEL_VALUE,"1.0",
    PANEL_NOTIFY_PROC,InvalidarAnalise,
    NULL);
  tfatorz=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Impedance normalization factor",
    PANEL_VALUE,"1.0",
    PANEL_NOTIFY_PROC,InvalidarAnalise,
    NULL);
  tngrau=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Estimated numerator degree  ",
    PANEL_NOTIFY_PROC,InvalidarAnalise,
    NULL);
  tdgrau=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Estimated denominator degree",
    PANEL_NOTIFY_PROC,InvalidarAnalise,
    NULL);
  sforcar=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Force degrees",
    PANEL_CHOICE_STRINGS,"yes","no",NULL,
    PANEL_VALUE,1,
    PANEL_NOTIFY_PROC,InvalidarDenominador,
    NULL);
  tdispden=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Denominator dispersion",
    PANEL_VALUE,"1e6",
    PANEL_NOTIFY_PROC,InvalidarDenominador,
    NULL);
  tdispnum=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Numerator dispersion  ",
    PANEL_VALUE,"1e6",
    PANEL_NOTIFY_PROC,InvalidarNumerador,
    NULL);
  sraizes=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Compute poles and zeros",
    PANEL_CHOICE_STRINGS,"yes","no",NULL,
    PANEL_VALUE,1,
    NULL);
  snorm=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Normalized results",
    PANEL_CHOICE_STRINGS,"yes","no",NULL,
    PANEL_VALUE,2,
    PANEL_NOTIFY_PROC,ZerarGrafico,
    NULL);
  tsaida=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Output node",
    PANEL_VALUE,1,
    PANEL_MIN_VALUE,0,
    PANEL_NOTIFY_PROC,InvalidarNumerador,
    NULL);
  botao=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Analyze",
    PANEL_NOTIFY_PROC,IniciarAnalise,
    NULL);
  window_fit(panel);
  window_fit(jparametros);
 
  jpfrequencia=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"Frequency Response Parameters",
    XV_X,6,
    XV_Y,57,
    NULL);
  panel=(Panel)xv_get(jpfrequencia,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  twmin=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Minimum frequency",
    PANEL_NOTIFY_PROC,ZerarGrafico,
    NULL);
  twmax=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Maximum frequency",
    PANEL_NOTIFY_PROC,ZerarGrafico,
    NULL);
  tgmin=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Minimum gain ",
    NULL);
  tgmax=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Maximum gain ",
    NULL);
  tfmin=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Minimum phase",
    PANEL_VALUE,"-180.0",
    NULL);
  tfmax=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Maximum phase",
    PANEL_VALUE,"180.0",
    NULL);
  tamin=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Minimum delay",
    PANEL_VALUE,"-10.0",
    NULL);
  tamax=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Maximum delay",
    PANEL_VALUE,"30.0",
    NULL);
  slog=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Scale",
    PANEL_CHOICE_STRINGS,"log","lin",NULL,
    PANEL_VALUE,0,
    PANEL_NOTIFY_PROC,ZerarGrafico,
    NULL);
  srads=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Units",
    PANEL_CHOICE_STRINGS,"Rd/s","Hertz",NULL,
    PANEL_VALUE,0,
    PANEL_NOTIFY_PROC,ZerarGrafico,
    NULL);
  splotar=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Plot",
    PANEL_CHOICE_STRINGS,"grid","phase","delay",NULL,
    PANEL_VALUE,7,
    PANEL_CHOOSE_ONE,FALSE,
    NULL);
  tsegmentos=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Segments",
    PANEL_VALUE,199,
    PANEL_MIN_VALUE,0,
    PANEL_MAX_VALUE,xxmax,
    PANEL_VALUE_DISPLAY_LENGTH,5,
    PANEL_NOTIFY_PROC,ZerarGrafico,
    NULL);
  botao=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Plot",
    PANEL_NOTIFY_PROC,IniciarResposta,
    NULL);
  window_fit(panel);
  window_fit(jpfrequencia);

  jedit=xv_create(jfrequencia,FRAME_CMD,
    XV_X,6,
    XV_Y,57,
    XV_LABEL,"Circuit Edition",
    NULL);
  panel=(Panel)xv_get(jedit,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  tenome=xv_create(panel,PANEL_MESSAGE,
    PANEL_LABEL_STRING,"Element",
    NULL);
  botao=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"-",
    XV_Y,5,XV_X,180,
    PANEL_NOTIFY_PROC,MudarElemento,
    NULL);
  bmais=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"+",
    XV_Y,5,XV_X,210,
    PANEL_NOTIFY_PROC,MudarElemento,
    NULL);
  botao=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Sweep..",
    XV_Y,5,XV_X,100,
    PANEL_NOTIFY_PROC,AbrirSweep,
    NULL);
  for (iii=0; iii<4; iii++)
    tvalor[iii]=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
      PANEL_LABEL_STRING,"value",
      PANEL_NOTIFY_PROC,AlterarValor,
      NULL);
  window_fit(panel);
  window_fit(jedit);

  jraizes=xv_create(jfrequencia,FRAME,
    XV_WIDTH,350, 
    XV_HEIGHT,239,
    XV_Y,240,
    XV_X,0,
    XV_LABEL,"Poles and Zeros",
    NULL);
  craizes=xv_create(jraizes,CANVAS,
    WIN_CMS,cms,
    CANVAS_X_PAINT_WINDOW,TRUE,
    CANVAS_REPAINT_PROC,PlotarPolosEZeros,
    NULL);
  
  xv_set(canvas_paint_window(craizes),
    WIN_EVENT_PROC,EventosPolosEZeros,
    WIN_CONSUME_EVENTS,
      WIN_ASCII_EVENTS,LOC_DRAG,LOC_MOVE,WIN_MOUSE_BUTTONS,
      WIN_TOP_KEYS,WIN_META_EVENTS,
      NULL,
    WIN_IGNORE_EVENTS,WIN_UP_EVENTS,WIN_UP_ASCII_EVENTS,
      NULL,
    NULL);

  jreferencia=xv_create(jfrequencia,FRAME_CMD,
    XV_X,6,
    XV_Y,57,
    XV_LABEL,"Function Files",
    NULL);
  panel=(Panel)xv_get(jreferencia,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  ttitulo=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Circuit",
    PANEL_NOTIFY_PROC,SetarNome,
    NULL);
  tnsaida=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Output node",
    PANEL_VALUE,1,
    PANEL_VALUE_DISPLAY_LENGTH,4,
    PANEL_NOTIFY_PROC,SetarNome,
    NULL);
  tnumerador=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Numerator  ",
    NULL);
  tdenominador=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Denominator",
    NULL);
  tzeros=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Zeros",
    NULL);
  tpolos=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Poles",
    NULL);
  botao=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Read",
    PANEL_NOTIFY_PROC,LerReferencia,
    NULL);
  window_fit(panel);
  window_fit(jreferencia);

  jdiretorio=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"Input file",
    XV_X,6,
    XV_Y,57,
  NULL);
  panel=(Panel)xv_get(jdiretorio,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  tnetlist=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Netlist",
    PANEL_NOTIFY_PROC,AbrirNetList,
    NULL);
  if (argc>1) {
    strcpy(get_text(tnetlist),argv[1]);
  }
  window_fit(panel);
  window_fit(jdiretorio);

  jsweep=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"Value Sweep",
    XV_X,106,
    XV_Y,156,
    NULL);
  panel=(Panel)xv_get(jsweep,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  tswval=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Value #",
    XV_Y,3,XV_X,130,
    PANEL_VALUE_DISPLAY_LENGTH,5,
    PANEL_VALUE,1,
    PANEL_MIN_VALUE,1,
    PANEL_MAX_VALUE,4,
    NULL);
  tswel=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Element", XV_Y,3, XV_X,3,
    PANEL_VALUE_DISPLAY_LENGTH,6,
    NULL);
  ssweep=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Min/max are",
    PANEL_CHOICE_STRINGS,"values","%",NULL,
    PANEL_VALUE,1,
    NULL);
  tswmin=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Minimum",
    PANEL_VALUE,"80.0",
    NULL);
  tswmax=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Maximum",
    PANEL_VALUE,"120.0",
    NULL);
  tswn=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Steps",
    PANEL_VALUE_DISPLAY_LENGTH,4,
    PANEL_VALUE,5,
    PANEL_MIN_VALUE,2,
    PANEL_MAX_VALUE,maxref,
    NULL);
  sescala=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Scale",
    PANEL_CHOICE_STRINGS,"lin","log",NULL,
    PANEL_VALUE,0,
    NULL);
  botao=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Start",
    PANEL_NOTIFY_PROC,ExecutarVarredura,
    NULL);
  window_fit(panel);
  window_fit(jsweep);
  
  jmontecarlo=xv_create(jfrequencia,FRAME_CMD,
    XV_X,6,
    XV_Y,57,
    XV_LABEL,"Monte Carlo analysis",
    NULL);
  panel=(Panel)xv_get(jmontecarlo,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  tmonten=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Number of circuits",
    PANEL_MIN_VALUE,0,
    PANEL_MAX_VALUE,maxref,
    PANEL_VALUE,20,
    NULL);
  tmontetr=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Variability    ",
    PANEL_VALUE,"0.05",
    NULL);
  tmontetlcm=xv_create(panel,PANEL_TEXT,PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_LABEL_STRING,"Variability: LC",
    PANEL_VALUE,"0.05",
    NULL);
  sdistribuicao=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Distribution",
    PANEL_CHOICE_STRINGS,"uniform","gaussian",NULL,
    PANEL_VALUE,1,
    NULL);
  botao=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Start",
    PANEL_NOTIFY_PROC,MonteCarlo,
    NULL);
  window_fit(panel);
  window_fit(jmontecarlo);

  ZoomOut();
  open_window(jfrequencia);
  xv_main_loop(jdiretorio);
  if (arquivo!=NULL) fclose(arquivo);
  exit(0);
}

/* End. */
