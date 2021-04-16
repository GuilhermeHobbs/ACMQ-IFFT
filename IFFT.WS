.ls1
.op
Program IFFT
------------

Bù Antoniï Carloó M® då Queiroz
Associatå Professor
Universidadå Federaì dï Riï då Janeiro

Documentation for version 1.3b

Thå  IFFÔ prograí analyseó lineaò circuits¬  computinç  transfeò 
functionó iî Laplacå transform® Froí thå transfeò funãtions¬  iî 
á  ratiï-oæ-polynomialó form¬ thå prograí caî computå poleó  anä 
zeroó aî ploô frequencù responså graphs® 

Thå  prograí  waó developeä aó á tooì foò fasô  verificátioî  oæ 
continuouó  timå  filteò designs® Iô ió alsï  usefuì  foò  otheò 
purposes¬ as:

-    Stabilitù analysió bù direcô poleó anä zeroó calculátion.
­    Studieó abouô frequencù compensatioî oæ amplifiers.
-    Studieó abouô compensatioî oæ operationaì amplifieò GÂ  anä 
     inpuô anä outpuô impedancå effectó iî filters® 
-    Studieó  abouô  thå effectó oæ parasitiã  capacitanceó  anä 
     resistanceó iî filters.
-    Montå  Carlï analysió anä studù oæ thå effecô oæ  componenô 
     variations.

User Interface:
---------------

Thå  prograí useó á graphicaì useò interfacå witè windows¬  thaô 
workó iî thå followinç way:

-    Tï  movå á window¬ presó thå lefô mouså buttoî anywherå  iî 
     thå  windo÷ framå anä movå thå mouså witè thå buttoî  pres
     sed.
-    Tï  resizå á window¬ presó thå righô mouså buttoî closå  tï 
     thå  righô bottoí corneò oæ thå windo÷ anä movå  thå  mouså 
     witè thå buttoî pressed.
-    Tï  closå á window¬ presó thå middlå mouså buttoî  anywherå 
     iî thå windo÷ framå.
-    Windo÷  movementó caî bå impossiblå duå tï  memorù  limita
     tions¬  anä iî theså caseó á beeğ sounds® Tï  freå  memory¬ 
     closå  somå  windows¬ puô windowó directlù oveò  thå  back
     ground¬ oò removå references.
-    Presó commanä buttonó witè thå lefô mouså button.
-    Accesó  texô fieldó pressinç thå lefô mouså buttoî  iî  thå 
     fielä  area® Thå mouså cursoò disappearó untiì  thå  Returî 
     keù ió pressed¬ endinç thå edition® Thå Esã keù clearó  thå 
     field¬ anä Ctrì-Ò recoveró thå lasô texô entered® Numericaì 
     fieldó worë iî thå samå way¬ buô thå editioî endó onlù wheî 
     á valiä numbeò ió entered.
-    Tï  opeî á menu¬ presó thå righô mouså buttoî oveò thå  in
     terfacå  objecô thaô havå thå desireä one® Selecô thå  iteí 
     movinç  thå mouså anä accepô iô bù pressinç thå lefô  mouså Š     button®  Tï  dismisó thå menõ withouô acceptinç  á  choice¬ 
     presó thå middlå mouså button® Á ">¢ aô thå righô oæ á menõ 
     iteí indicateó thaô therå ió á submenu¬ accessiblå bù pres
     sinç thå righô mouså buttoî again.
-    Onlù thå controló iî totallù exposeä windowó arå immediatå
     lù accessible® Aî attempô tï accesó á controì iî á partiaì
     lù  covereä  windo÷ wilì firsô causå itó  movemenô  tï  thå 
     front¬ iæ possible.

Á  mouså  ió requireä foò optimaì performance¬ buô  thå  prograí 
includeó  á mouså emulatoò driveî froí thå keyboard® Thå  cursoò 
keyó commanä thå emulateä mouså cursor® Thå keyó Return¬  Space¬ 
anä Esã emulatå thå mouså buttonó left¬ middle¬ anä right¬  res
pectively®  Thå cursoò steğ ió selecteä bù thå keyó  Home¬  PgDî 
anä  PgUp® Wheî thå Shifô keù ió presseä oò CapsLocë ió  active¬ 
thå buttonó worë iî togglå mode¬ sï á buttoî continuouslù  pres
seä  caî bå simulated® Thå mouså emulatoò ió disabled¬  anä  thå 
keyboarä workó normallù wheî ScrollLocë ió active.

Thå maiî interfacå elemenô oæ thå prograí ió á menu¬  accessiblå 
iî thå frameó oæ alì thå windows® Alì thå functionó caî bå staò
teä  froí there® Somå opeî dialoç boxes¬ somå  acô  immediately¬ 
anä  somå havå submenus® Thå prograí alwayó giveó somå  feedbacë 
afteò anù command® Therå arå somå speciaì commandó noô listeä iî 
thå menuó anä dialoç boxes¬ listeä below.

Á  twï-buttonó mouså caî alsï bå used® Windowó anä menuó caî  bå 
dismisseä bù pressinç botè buttonó simultaneously.
 
Keyboard commands in the frequency response graph:
--------------------------------------------------

A/R - Reduces/increases the maximum frequency.
</> - Moves down/up the frequency range.
+/- - Reduces/increases the maximum gain.
G - Toggles the drawing of a grid.
F - Toggles the plotting of phase curves.
T - Toggles the plotting of group delay curves.
L - Frequency scale logarithmic/linear.
Vertical arrows - Move the gain curve.
Horizontal arrows - Move the cursor.
Ctrl- horizontal arrows - Move the cursor faster.
Tab - Changes the selected gain curve.
Ú ­ Zoom ouô.

Keyboarä commandó in the poles and zeros graph:
-----------------------------------------------

Arrows- Move the plot.
+/- - zoom in/out. 

Mouså commands:
---------------

Iî thå twï graphs¬ thå mouså moveó á cursoò anä controló á  zooí Šfunction.

Input:
------

Thå prograí beginó bù openinç thå frequencù responså windo÷  anä 
thå  directorù window® Iî thå directorù window¬ á  netlisô  filå 
namå  caî bå selecteä witè thå mouså (lefô button© oò typeä  di
rectly®  Thå masë fielä caî bå useä anytimå tï looë aô disë  di
rectories®  Thå netlisô fielä caî bå useä anytimå tï changå  thå 
circuiô beinç analyzed.

Thå  prograí acceptó aó inpuô á circuiô descriptioî filå iî  thå 
formaô generateä bù thå EdFiì editoò program® Iô ió á texô  filå 
witè  thå followinç format® Alì thå elemenô valueó iî Ohms¬  Fá
rads¬ Henrys¬ Amperes¬ anä Volts:

Firsô lineº Numbeò oæ nodes¬ excludinç thå referencå (nodå 0).
Followinç linesº Onå elemenô peò line:

-    Resistor:
     R<name> <node1> <node2> <R>
-    Inductor:
     L<name> <node1> <node2> <L>
-    Capacitor:
     C<name> <node1> <node2> <C>
-    Transformeò witè inductanceó L11¬ L22¬ M1² [¬ M21İ (M21=M1² 
     ió thå default):
     N<name> <node1+> <node1-> <node2+> <node2-> <L11> <L22> <M12> [<M21>] 
-    Gyrator, with gyration resistance Rg:
     Y<name> <node1+> <node1-> <node2+> <node2-> <Rg>
-    Voltage controlled voltage source (voltage amplifier):
     E<name> <nodeV+> <nodeV-> <nodev+> <nodev-> <Av>
-    Current controlled current source (current amplifier):
     F<name> <nodeI+> <nodeI-> <nodei+> <nodei-> <Ai>
-    Voltage controlled current source (transconductor):
     G<name> <nodeI+> <nodeI-> <nodeV+> <nodeV-> <Gm>
-    Current controlled voltage source (transresistor):
     H<name> <nodeV+> <nodeV-> <nodei+> <nodei->
-    Operationaì  amplifier¬  witè gaiî GB/ó (GÂ iî  rad/s©  anä 
     outpuô resistancå Ro:
     A<name> <node-> <node+> <output node> <GB> <Ro>
-    Ideal operational amplifier: nullator-norator model: 
     O<name> <input node 1> <input node 2> <output node>
-    Bipolar transistor: hybrid h model
     Q<name> <nodeC> <nodeB> <nodeE> <hfe> <hie> <hre> <hoe>
-    MOS transistor:
     M<name> <nodeD> <nodeG> <nodeS> <Gm> <Gds>
-    Current source:
     I<name> <node+> <node-> <I>
-    Voltage source:
     V<name> <node+> <node-> <V>
-    Voltage source with series resistor (V=1 is the default):
     Z<name> <node-> <node+> <Rs> [<V>]
ŠOtheò elementó caî bå builô witè combinationó oæ theså elements® 
Notå thaô thå transistoò modeló dï noô includå capacitances¬ buô 
theù  caî  bå  addeä explicitly® Notå  alsï  thaô  thå  currenô-
controlleä sourceó havå thå currenô iî á shorô-circuiô brancè aó 
inpuô®

Analysió method:
----------------

Thå prograí operateó witè á versioî oæ thå modifieä nodaì analù
sió  method¬ sï thå currentó iî voltagå sourceó anä iî  controì
linç  shorô circuitó arå computed® Theiò valueó caî bå  accesseä 
aó "nodaì voltages¢ iî nodeó abovå thå lasô nodå oæ thå circuit® 
Thå  prograí listó whilå readinç thå netlisô whaô arå  thå  nodå 
numberó  assigneä tï eacè current® Ideaì operationaì  amplifieró 
arå  treateä aó nullatoò-noratoò pairs iî á morå efficienô  way¬ 
anä theiò outpuô currentó arå noô computed® 

Wheî  thå  Analyzå buttoî iî thå analysió parameteró  windo÷  ió 
pressed¬  thå  circuiô ió analyzeä iî á  numbeò  oæ  frequencieó 
equallù  spaceä oveò thå uniô circle® Froí thå obtaineä  values¬ 
thå numeratoò anä denominatoò polynomialó iî "s¢ oæ thå transfeò 
functionó  iî  Laplacå transforí arå recovereä bù  Fasô  Fourieò 
Transformó (FFT)¬ anä listeä iî thå messageó window® Thå complå
tå analysió ió madå onlù wheî changeó iî thå analysió parameteró 
invalidatå anterioò analysió results.

Thå methoä ió precise¬ buô caî presenô numericaì problemó iæ thå 
circuiô ió noô adequatelù normalized® Iî thå analysió parameteró 
windo÷ therå arå somå fieldó thaô caî bå initializeä witè valueó 
thaô  controì thå precisioî oæ thå analysis® Thå defaulô  valueó 
arå  usuallù convenienô foò normalizeä circuits® Thå meaninç  oæ 
thå itemó iî thió windo÷ are:

-    Frequencù  normalizatioî factorº Factoò useä  tï  normalizå 
     thå circuiô iî frequency® Thå ideaì valuå ió thå  geometré
     caì  meaî oæ thå circuiô poleó anä zeros® Afteò thå  analù
     sis¬  thå prograí listó whaô woulä bå thå ideaì valueó  foò 
     thå  numeratoò  anä denominator¬ iæ applicable®  Foò  usuaì 
     circuits¬  thå  useä valuå musô bå withiî á decadå  oæ  thå 
     ideaì  valueó foò reliablå results® Somå variationó oî  thå 
     factoò  tï verifù iæ thå prograí insistó iî thå samå  ideaì 
     valueó  ió recommendeä wheî iî thå analysió oæ  higè  ordeò 
     circuitó witè poleó anä zeroó spreaä oveò severaì magnitudå 
     orders.
-    Impedancå  normalizatioî factorº Factoò useä  tï  normalizå 
     thå circuiô iî impedance® Thå samå observationó apply.
-    Estimateä  numeratoò anä denominatoò degreesº  Thå  prograí 
     computeó thå maximuí possiblå denominatoò degreå foò volta
     gå  transfeò  functionó iî thå circuiô baseä  oî  á  normaì 
     tree¬ listeä afteò thå netlisô iî thå messageó window® Thió 
     valuå  ió  correcô foò noî-pathologicaì circuits¬  anä  thå 
     prograí wilì noô accepô aó valiä anù analysió resultinç  iî 
     á  differenô value® Thå estimateä numeratoò degreå musô  bå 
     seô  bù thå useò iæ thå optioî oæ forcinç degreeó ió  used® Š     Iî  circuitó wherå thå numeratoò degreå ió higheò thaî  thå 
     denominatoò degree¬ thå numeratoò degreå musô bå seô tï thå 
     correcô value¬ oò thå analysió maù resulô wrong.
-    Forcå degreeó option¬ anä numeratoò anä denominatoò disper
     sioî  factorsº Thå analysió methoä produceó polynomialó  oæ 
     degreeó  thaô caî bå higheò thaî thå correcô ones¬  anä  sï 
     musô bå cleaneä oæ numericaì residues® Thå dispersioî  fac
     toró caî bå useä foò thió purpose® Theù definå thå  maximuí 
     allowablå ratiï amonç polynomiaì coefficientó (normalized)¬ 
     anä  arå useä tï eliminatå toï smalì coefficientó froí  thå 
     polynomials®  Thå defaulô settingó arå usuallù  enougè  foò 
     normalizeä circuits® Iî somå cases¬ iô ió morå practicaì tï 
     directlù  forcå thå numeratoò anä denominatoò  degreeó  (tï 
     thå estimateä values¬ thaô musô bå known)¬ aó iî thå analy
     sió  oæ  compleø amplifieró witè manù  naturaì  frequencieó 
     widelù spaced¬ oò circuitó witè nonideaì operationaì ampli
     fiers.

References:
-----------

Frequencù  responså  plots¬ anä poleó anä zeroó  plots¬  caî  bå 
compareä  witè saveä references® Thå referenceó caî bå  obtaineä 
froí thå presenô analysió oò froí saveä files® Iô ió possiblå tï 
analyzå á circuit¬ savå thå resultó aó á reference¬ ediô somå oæ 
thå componenô values¬ reanalize¬ anä ploô thå ne÷ resultó compá
reä witè thå saveä ones® Thå referenceó arå enumerateä froí ± tï 
á maximuí oæ 250 oò less¬ dependinç oî thå availablå memory® Thå 
referenceó  arå  alsï useä iî thå valuå sweeğ  anä  Montå  Carlï 
analysis.

Edition:
--------

Thå circuiô valueó caî bå editeä iî thå ediô window® Thå editioî 
causeó  thå invalidatioî oæ thå lasô analysis¬ anä  thå  circuiô 
musô bå reanalized® Thå editeä circuiô cannoô bå saved®

Sweep:
------

Therå  ió aî optioî oæ sweepinç á valuå oveò á  specifieä  rangå 
(iî  thå ediô window)® Thå råsultó arå saveä aó references¬  anä 
subsequenô plottinç commandó producå familieó oæ curveó  showinç 
thå results® Thå sweeğ rangå caî bå specifieä bù absolutå limitó 
oò  percentageó oæ thå normaì value® Thå sweeğ caî bå lineaò  oò 
logarithmic®  Thå originaì circuiô ió retained¬ buô musô bå  rå
analizeä  iæ itó curveó arå tï appeaò iî thå plots® Alì thå  re
ferenceó arå cleareä beforå á sweep.

Montå Carlï analysis:
---------------------

Á   seô  oæ  circuitó  witè  elemenô  valueó  withiî   specifieä 
toleranceó  ió  automaticallù generateä anä  analyzed®  Alì  thå Šresultó arå storeä aó references¬ aó iî thå sweeğ analysis®  Thå 
variabilitieó  oæ  certaiî groupó oæ elementó caî  bå  specifieä 
independently¬  anä  uniforí oò Gaussiaî  distributionó  caî  bå 
used® Iî thå Gaussiaî distribution¬ thå specifieä  variabilitieó 
corresponä tï threå standarä deviations® Therå ió á menõ iteí iî 
thå referenceó submenõ thaô caî bå useä tï savå alì thå frequen
cù  responses¬ poles¬ anä zeroó resultinç froí thå  analysió  tï 
files®  Thå  fileó caî bå useä foò comparisoî witè  thå  resultó 
obtaineä bù sensitivitù analysió witè thå SENSÉ program¬ bù  thå 
uså oæ thå CPSENSÉ anä CPSPÚ programs® (Seå thå SENSÉ packagå aô 
thå ftğ sitå coe.ufrj.br¬ directorù pub/acmq.)

Outpuô files:
------------

Alì  thå resultó caî bå saved¬ iî separatå texô fileó  accordinç 
tï thå typå oæ result® Thå nameó arå giveî automatically® Iô  ió 
alsï possiblå tï savå alì thå messageó iî thå messagå windo÷  aó 
á file® Thå polynomialó anä rootó arå saveä iî normalizeä  form® 
Thå  normalizatioî factoò useä ió alsï saveä aô thå enä  oæ  thå 
files® Thå referencå poleó anä zeroó arå saveä unnormalized.

Observations:
-------------

Thå prograí caî havå problemó iî findinç poleó anä zeroó iî somå 
higè-ordeò circuits® Iî theså caseó iô wilì loweò thå  tolerancå 
oæ thå rootó untiì iô caî solvå foò them¬ anä thå finaì  resultó 
maù bå inaccurate® Iô ió importanô tï turî oî thå automatiã polå 
anä  zerï  computatioî (iî thå analysió window©  onlù  wheî  thå 
frequencù normalizatioî factoò ió correctlù adjusted¬  otherwiså 
aî  irrecoverablå  overflo÷ erroò maù occur® Foò  comparisoî  oæ 
results¬ thå prograí caî uså twï differenô methodó foò computinç 
polynomiaì  rootó (seô iî thå rooô parameteró window)®  Thå  då
faulô  methoä ió thå mosô reliable¬ anä slower¬ one®  Thå  poleó 
anä  zeroó  optioî iî thå maiî menõ causeó  thå  computatioî  oæ 
poleó anä zeroó oæ thå presenô functioî anä oæ alì thå  refereî
ces¬  iæ  theù  werå noô alreadù computed®  Thå  changinç  oæ  á 
parameteò iî thå rootó parameteró windo÷ causeó thå invalidatioî 
oæ thå poleó anä zeroó oæ thå presenô function¬ buô noô thå oneó 
oæ thå references® Thió ió tï allo÷ easù comparisoî oæ results.

Thå  prograí wilì drivå anù graphiã boarä supporteä bù thå  .BGÉ 
graphiã  driveró  (Turbï Pascaì 7.0)¬ uğ tï  640x48°  1¶  coloró 
mode®  Thå highesô resolutioî modå wilì bå useä bù default¬  buô 
thió caî bå overriddeî iî thå commanä line:

		>IFFT <file> <driver> <mode>

Thió  wilì copù thå namå <file¾ tï thå netlisô namå texô  field¬ 
anä initializå thå graphiã systeí witè thå driveò anä modå  nuí
beró giveî (Exº "± 1¢ ½ CGÁ 320x20° (...)¬ "± 4¢ ½ CGÁ  640x200¬ 
"³  1¢  ½ EGÁ 640x350¬ "² 5¢ ½ MCGÁ 640x480¬ etc.©  Thå  commanä 
linå commandó arå optional® Thå graphicó driveró musô bå oî  thå 
cuòrenô directorù oò iî á patè pointeä bù thå environmenô variaŠblå TPBGÉ (Uså thå DOÓ "set¢ commanä tï creatå it)®

Thå  IFFÔ  prograí ió iî continuouó evolutioî  sincå  itó  firsô 
version¬  writteî  iî BASIÃ foò aî HĞ-7µ computeò iî  1984®  Thå 
prograí  waó porteä tï á PC¬ rewritteî iî Turbï Pascal¬  anä  iî 
199²  rewritteî witè thå ne÷ graphicaì interface¬ alsï iî  Turbï 
Pascal® 

The EdFil editor program:
-------------------------

Thå EdFiì editoò caî bå useä tï generatå thå inpuô neô-lisô filå 
foò  thå IFFÔ program¬ anä alsï foò otheò programs¬  eveî  SPICÅ 
(witè somå editing)® Iô waó writteî afteò thå conclusioî thaô iô 
ió  virtuallù impossiblå tï writå á textuaì netlisô foò  á  noî-
triviaì  circuiô withouô errors® Itó uså ió recommendeä foò  anù 
circuiô analysis.

Thå circuiô ió drawî oî thå screeî usinç thå cursoò keyó anä thå 
selecteä  keyboarä  keyó  listeä aô thå  bottoí  oæ  thå  editoò 
screen® Á helğ screeî ió assesseä bù thå ¿ key® Nameó anä  para
meteró  foò thå elementó arå giveî bù movinç thå cursoò  tï  thå 
componenô anä touchinç thå Returî key¬ oò bù Ctrì-X¬ thaô causeó 
thå prograí tï asë paramåteró foò alì thå visiblå elements®  Thå 
besô methoä ió usuallù tï firstlù dra÷ alì thå circuiô anä lateò 
givå thå parameters® Therå arå dåfaulô nameó anä paramåteró  foò 
alì  elements® Thå parameteró arå á text¬ anä arå reprïduceä  iî 
thå neô-lisô aó given¬ unlesó foò formulae¬ thaô musô bå  enclo
seä iî parenthåsis.

Oncå  drawî thå circuit¬ thå neô-lisô ió generateä witè  Ctrì-Q® 
Thå  prograí theî askó thå nameó oæ thå fileó wherå tï savå  thå 
circuiô  descriptioî (.ciò file© anä thå neô-lisô  (.neô  file)® 
Afteò this¬ anù prograí caî bå executeä whilå thå editoò remainó 
residenô  iî memory¬ witè executioî returninç lateò tï thå  edé
tor® 

Aî importanô featurå oæ thå prograí ió thå optionaì uså oæ  foò
mulaå iî thå parameters® Anù mathematicaì expressioî usinç conó
tantó anä valueó giveî iî á valuå lisô caî bå useä foò á numeré
caì  parameter®  Thå expressionó arå evaluateä iî  thå  neô-lisô 
generation® Thió allowó easù uså oæ componenô valuå listó  genå
rateä bù synthesió programs¬ oò eveî thå uså oæ EdFiì aó á  syî
thesió  program¬  witè componentó parameteró  giveî  bù  projecô 
formulae®  Thå  "=¢ sigî caî bå useä iî formulaó tï  creatå  ne÷ 
valueó iî thå valuå list® Uså resistoró witè botè nodeó groundeä 
tï creatå setó oæ valueó iî thió way¬ anä operatå thå prograí aó 
á simplå spreadsheet® Evaluatioî ió froí bottoí tï top¬ lefô  tï 
right.

Thå  defaulô screeî modå selectioî caî bå overriddeî aó  iî  thå 
IFFÔ  program®  Thå .BGÉ fileó musô bå presenô  oî  thå  defaulô 
drivå oò iî thå patè indicateä bù thå DOÓ variablå TPGBI.

Contactinç thå author:Š----------------------

Commentó  anä  doubtó abouô thå programó shalì bå  senô  tï  thå 
author:

Dr. Antonio Carlos M. de Queiroz
Programa de Engenharia Eletrica - COPPE
Universidade Federal do Rio de Janeiro
CP 68504
21945-970 Rio de Janeiro, RJ, Brazil
E-mail: acmq@coe.ufrj.bò
FTPº coe.ufrj.br¬ directorù pub/acmq
WWWº http://www.coe.ufrj.br/gpas/acmq.html 

Files on the distributioî compresseä file:
------------------------------------------

IFFT-1.EXE: Reaì modå version (anù PC).
IFFT.EXEº Protecteä modå versioî (38¶ up¬ 10° references).
EDFIL.EXE: Circuit editor program.
*.BGI: Graphics drivers.
LITT.CHR: Font for the messages window.
*.CIR: Circuit files em EdFil format.
*.NET: NetList files.
*.VAL: Value list files for EdFil.
*.TXTº Documentation.
RTM.EXE¬ DPMI16BI.OVLº Protecteä modå drivers.

Licensing
---------

Thå IFFÔ prograí caî bå useä anä distributeä freå oæ charge¬ foò 
educationaì purposes¬ aó lonç aó iô ió noô changed¬ anä referen
cå ió madå iî anù worë donå witè itó help® Alì otheò rightó  arå 
reserved® Foò commerciaì uses¬ contacô thå author.

Thå authoò believeó thaô thå prograí workó correctly¬ buô cannoô 
bå  responsiblå  foò  anù losseó duå tï  possiblå  bugó  iî  thå 
prograí thaô escapeä hió attention.

Useró  arå encourageä tï senä tï thå authoò á letteò  oò  å-maiì 
messagå  tellinç wherå thå prograí ió beinç used¬ anä  foò  whaô 
purpose.

Versioî information
-------------------

Versioî 1.3bº Á buç iî thå inclusioî oæ amplifieró iî thå normaì 
treå waó corrected.
Versioî 1.3aº Á buç iî Gdó iî thå MOÓ transistoò waó corrected.
Versioî  1.3º  Complexitù ordeò estimatioî improveä  bù  á  morå 
generaì  algorithí  foò thå generatioî oæ thå normaì  tree®  Thå 
prograí  wilì noô anymorå underestimatå thå order®  Montå  Carlï 
analysió introduced.
ŠACMQ - 17 October 1996
