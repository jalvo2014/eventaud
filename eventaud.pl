#!/usr/local/bin/perl -w
#------------------------------------------------------------------------------
# Licensed Materials - Property of IBM (C) Copyright IBM Corp. 2010, 2010
# All Rights Reserved US Government Users Restricted Rights - Use, duplication
# or disclosure restricted by GSA ADP Schedule Contract with IBM Corp
#------------------------------------------------------------------------------

#  perl eventaud.pl
#
#  Summarize Situation Event Status from TSITSTSH
#
#  john alvord, IBM Corporation, 8 Devember 2017
#  jalvord@us.ibm.com
#
# tested on Windows Activestate 5.16.2
# Should work on Linux/Unix but not yet tested
#
# $DB::single=2;   # remember debug breakpoint
#     use re 'debug';
## todos
## Add eventaud.ini, especially added table sizes

#use warnings::unused; # debug used to check for unused variables
use strict;
use warnings;

# See short history at end of module

my $gVersion = "1.38000";
my $gWin = (-e "C://") ? 1 : 0;    # 1=Windows, 0=Linux/Unix

use Data::Dumper;               # debug only
use Time::Local;

# a collection of variables which are used throughout the program.
# defined globally

my $args_start = join(" ",@ARGV);      # capture arguments for later processing
my $run_status = 0;                    # A count of pending runtime errors - used to allow multiple error detection before stopping process

my $traceon = 0;

# some common variables

my $rc;
my @words = ();
my $ll;
my $oneline;
my $sx;
my $f;
my $g;
my $h;

my %sitagtx;
my $sitagt_ref;

my %sitsx;                      # track most recent situation start time

my %missatomx;

my %nodex;

my $event_min = 0;
my $event_max = 0;
my $event_dur = 0;

my %seq999;

my %seq998;

my %timex;                               #hash to hold time based records at different levels

my $local_diff = 0;

my $ack_ct = 0;



# forward declarations of subroutines

sub init;                                # read command line and ini file
sub logit;                               # queue one record to survey log
sub datadumperlog;                       # dump a variable using Dump::Data if installed
sub get_time;                            # get time
sub get_epoch;                           # get epoch from ITM stamp
sub init_all;                            # input from txt or lst files
sub newsit;                              # create new situation entry
sub parse_lst;                           # parse the KfwSQLClient output
sub sec2time;
sub setload;                             # account for workload by time
sub setbudget;                            # account for workload by time

my %advsitx;

my $full_logfn;
my $logfn;

my %sitfullx = ();                        # Index from situation index to Fullname
my %epochx = ();

# Situation related data

my $siti = -1;                             # count of situations
my $curi;                                  # global index for subroutines
my @sit = ();                              # array of situations
my %sitx = ();                             # Index from situation name to index
my @sit_pdt = ();                          # array of predicates or situation formula
my @sit_fullname = ();                     # array of fullname
my @sit_psit = ();                         # array of printable situation names
my @sit_sitinfo = ();                      # array of SITINFO columns
my @sit_autostart = ();                    # array of AUTOSTART columns
my @sit_reeval = ();                       # Sampling interval in seconds
my @sit_tfwd = ();                         # when 1, event forwarding enabled
my $sit_forwarded = 0;                     # when >0 some event forwarding is taking place

my @sit_atomize = ();
my $sit_time_min = "";
my $sit_time_max =  "";

# option and ini file variables variables

my $opt_txt;                    # input from .txt files
my $opt_txt_tsitdesc;           # TSITDESC txt file
my $opt_txt_tsitstsh;           # TSITSTSH txt file
my $opt_txt_tname;              # TNAME txt file
my $opt_lst;                    # input from .lst files
my $opt_lst_tsitdesc;           # TSITDESC lst file
my $opt_lst_tsitstsh;           # TSITDESH lst file
my $opt_lst_tname;              # TNAME lst file
my $opt_lst_tems = "";
my $opt_log;                    # name of log file
my $opt_ini;                    # name of ini file
my $opt_debuglevel;             # Debug level
my $opt_debug;                  # Debug level
my $opt_v;                      # verbose flag
my $opt_o;                      # output file
my $opt_tsitstsh;               # name of TSITSTSH file
my $opt_odir;                   # Directory for output file
my $opt_workpath;               # Directory to store output files
my $opt_syntax;                 # syntax tracing
my $opt_sum;                    # When 1 create summary file
my $opt_nohdr;                  # skip printing header
my $opt_allresults;                # when 1 show maximum detail report
my $opt_time;                   # when 1 add in all results to each all line report
my $opt_days;                   # How many days to look backward, default 2 days
my $opt_dgrace;
my $opt_crit = "";
my $critical_fn = "eventaud.crit";
my @crits;


# following structures used to calculate a result/event budget
# %budget has a typical node/situation/displayitem/detail

my %budget_situationx;
my $budget_total_ref;
my $total_key = "_total_";
my $budget_situation_ref;
my $irowsize;

my %budget_thrunodex;
my $budget_thrunode_ref;

my %budget_nodex;
my $budget_node_ref;
my %budget_sitnodeatomx;                    # summarize by situation/node/atom
my $budget_sitnodeatom_ref;
my %budget_sitnodex;                        # summarize by situation/node
my $budget_sitnode_ref;
my %budget_sitx;                            # summarize by situation
my $budget_sit_ref;

my %situation_dupx;
my %situation_dnullx;
my %situation_nullx;
my %situation_missx;
my %situation_mergex;
my $null_ct = 0;
my $dnull_ct = 0;
my $dup_ct = 0;
my $merge_ct = 0;
my $miss_ct = 0;

my $budget_events = 0;
my $budget_results = 0;
my $budget_results_bytes = 0;
my $budget_pure_events = 0;
my $budget_pure_results_bytes = 0;
my $budget_pure_results = 0;
my $budget_pure_hidden_tems_merge = 0;
my $budget_pure_hidden_tems_merge_bytes = 0;
my $budget_pure_hidden_missing_displayitem = 0;
my $budget_pure_hidden_missing_displayitem_bytes = 0;
my $budget_pure_hidden_duplicate_displayitem = 0;
my $budget_pure_hidden_duplicate_displayitem_bytes = 0;
my $budget_pure_hidden_null_displayitem = 0;
my $budget_pure_hidden_null_displayitem_bytes = 0;

my $budget_samp_events = 0;
my $budget_samp_results = 0;
my $budget_samp_results_bytes = 0;
my $budget_samp_results_confirms = 0;
my $budget_samp_results_confirms_bytes = 0;
my $budget_samp_hidden_missing_displayitem = 0;
my $budget_samp_hidden_missing_displayitem_bytes = 0;
my $budget_samp_hidden_duplicate_displayitem = 0;
my $budget_samp_hidden_duplicate_displayitem_bytes = 0;
my $budget_samp_hidden_null_displayitem = 0;
my $budget_samp_hidden_null_displayitem_bytes = 0;

# produce output report
my @oline = ();
my $cnt = -1;
my @sline = ();                              # summary lines
my $sumi = -1;

my $hdri = -1;                               # some header lines for report
my @hdr = ();                                #

# allow user to set impact
my %advcx = (
              "EVENTAUDIT1001W" => "75",
              "EVENTAUDIT1003W" => "20",
              "EVENTAUDIT1004W" => "40",
              "EVENTAUDIT1005W" => "10",
              "EVENTAUDIT1006W" => "10",
              "EVENTAUDIT1007W" => "80",
              "EVENTAUDIT1008E" => "100",
              "EVENTAUDIT1009W" => "50",
              "EVENTAUDIT1010W" => "25",
              "EVENTAUDIT1011W" => "65",
              "EVENTAUDIT1012W" => "85",
              "EVENTAUDIT1013W" => "50",
              "EVENTAUDIT1014E" => "90",
              "EVENTAUDIT1015W" => "75",
              "EVENTAUDIT1016W" => "80",
              "EVENTAUDIT1017I" => "25",
           );

# Following table can be used to calculate result
# row sizes. This was adopted from a terrific
# historical data estimator workspace.
# It doesn't have every table, especially not ones
# created by Agent Builder or Universal Agent, but
# it is a good resource.

my %htabsize = (
   'ACTSRVPG'    => '376',
   'ADRSPACS'    => '338',
   'AGENE64'     => '328',
   'AGENED32'    => '352',
   'AGENED64'    => '352',
   'AGENERIC'    => '316',
   'AGGREGATS'   => '3368',
   'AIXMPIOATR'  => '560',
   'AIXMPIOSTS'  => '560',
   'AIXNETADPT'  => '1592',
   'AIXPAGMEM'   => '208',
   'AIXSYSIO'    => '144',
   'APPL'        => '198',
   'APPL_DSDET'  => '126',
   'ASCPUUTIL'   => '316',
   'ASCSOWN'     => '692',
   'ASREALSTOR'  => '142',
   'ASRESRC2'    => '97',
   'ASSUMRY'     => '375',
   'ASVIRTSTOR'  => '64',
   'BALG'        => '176',
   'BPXPRM2'     => '92',
   'BUFPOOLS'    => '276',
   'CACHE_CU'    => '331',
   'CACHE_DEV'   => '649',
   'CACHE_SET'   => '175',
   'CACUGDEV'    => '606',
   'CF_DS'       => '182',
   'CF_DSO'      => '130',
   'CHAN_PATH'   => '390',
   'CHANNEL'     => '320',
   'CHNPATHS'    => '364',
   'CICSACD'     => '263',
   'CICSAFC'     => '55',
   'CICSAFD'     => '609',
   'CICSAID'     => '86',
   'CICSBNA'     => '182',
   'CICSBND'     => '563',
   'CICSBNP'     => '616',
   'CICSBNS'     => '65',
   'CICSCBS'     => '65',
   'CICSCDM'     => '168',
   'CICSCDP'     => '184',
   'CICSCDS'     => '144',
   'CICSCND'     => '168',
   'CICSCOS'     => '228',
   'CICSCSD'     => '208',
   'CICSD2S'     => '90',
   'CICSD2T'     => '92',
   'CICSDAT'     => '65',
   'CICSDJD'     => '352',
   'CICSDLS'     => '144',
   'CICSDMP'     => '93',
   'CICSDTD'     => '386',
   'CICSEBD'     => '340',
   'CICSEPD'     => '260',
   'CICSEVD'     => '176',
   'CICSEVS'     => '77',
   'CICSEXD'     => '106',
   'CICSFCA'     => '53',
   'CICSFCS'     => '76',
   'CICSHSD'     => '169',
   'CICSICE'     => '103',
   'CICSICO'     => '112',
   'CICSIPC'     => '348',
   'CICSIST'     => '48',
   'CICSJAT'     => '103',
   'CICSJCC'     => '109',
   'CICSJPG'     => '341',
   'CICSJPR'     => '309',
   'CICSJVM'     => '77',
   'CICSJVP'     => '88',
   'CICSJVS'     => '112',
   'CICSLPS'     => '134',
   'CICSLSA'     => '154',
   'CICSMTG'     => '180',
   'CICSMTR'     => '121',
   'CICSNQA'     => '845',
   'CICSPIS'     => '57',
   'CICSPND'     => '140',
   'CICSPPD'     => '238',
   'CICSPPH'     => '295',
   'CICSPTD'     => '70',
   'CICSRDS'     => '136',
   'CICSRMG'     => '180',
   'CICSROV'     => '216',
   'CICSRQS'     => '301',
   'CICSRTE'     => '217',
   'CICSRTS'     => '220',
   'CICSSCR'     => '432',
   'CICSSDP'     => '191',
   'CICSSIA'     => '131',
   'CICSSTOR'    => '96',
   'CICSTCA'     => '80',
   'CICSTDQ'     => '88',
   'CICSTDS'     => '62',
   'CICSTFL'     => '245',
   'CICSTIP'     => '186',
   'CICSTMR'     => '260',
   'CICSTPS'     => '384',
   'CICSTR1'     => '366',
   'CICSTR2'     => '245',
   'CICSTR3'     => '245',
   'CICSTRD'     => '263',
   'CICSTRE'     => '138',
   'CICSTRF'     => '228',
   'CICSTRN'     => '158',
   'CICSTRP'     => '149',
   'CICSTRR'     => '80',
   'CICSTRS'     => '137',
   'CICSTRT'     => '309',
   'CICSTRU'     => '161',
   'CICSTSA'     => '162',
   'CICSTSD'     => '172',
   'CICSTSG'     => '101',
   'CICSTSS'     => '86',
   'CICSTSV'     => '52',
   'CICSTSX'     => '212',
   'CICSTTS'     => '233',
   'CICSUDF'     => '135',
   'CICSURG'     => '96',
   'CICSURS'     => '75',
   'CICSUWA'     => '56',
   'CICSUWE'     => '74',
   'CICSUWL'     => '422',
   'CICSWBS'     => '155',
   'CICSWRD'     => '220',
   'CICSXMD'     => '624',
   'CICSXMS'     => '90',
   'CICSXSV'     => '52',
   'CLACTRMT'    =>'7452',
   'COMSTOR'     => '339',
   'CON'         => '339',
   'CTGCAD'      => '277',
   'CTGCMS'      => '80',
   'CTGCSD'      => '88',
   'CTGCSS'      => '96',
   'CTGDSD'      => '242',
   'CTGGDS'      => '116',
   'CTGROV'      => '152',
   'CTGRTD'      => '235',
   'CTGRTS'      => '240',
   'CTGTRA'      => '124',
   'CTGTRD'      => '506',
   'CTGWTS'      => '72',
   'CTLUNIT'     => '460',
   'DA_ALCSUM'   => '154',
   'DA_BLKSUM'   => '128',
   'DA_CASSUM'   => '202',
   'DA_CATSUM'   => '132',
   'DA_CISSUM'   => '202',
   'DA_CRTSUM'   => '128',
   'DA_EXTSUM'   => '154',
   'DA_IBKSUM'   => '154',
   'DA_MATSUM'   => '186',
   'DA_NEWSUM'   => '146',
   'DA_NRFSUM'   => '166',
   'DA_ORGDTL'   => '154',
   'DA_ORGSUM'   => '156',
   'DA_REFSUM'   => '128',
   'DA_SMSDTL'   => '180',
   'DA_SMSSUM'   => '154',
   'DA_SYSSUM'   => '414',
   'DA_UNCDTL'   => '146',
   'DA_UNCSUM'   => '94',
   'DA_UNUSUM'   => '154',
   'DAG_SUMM'    => '446',
   'DAGDSNDTL'   => '603',
   'DASD_MVS'    => '1170',
   'DASD_SUMM'   => '905',
   'DASDCACHE'   => '756',
   'DASDLOG'     => '201',
   'DASDMVSDEV'  => '192',
   'DASDPERF'    => '537',
   'DASDSPAC'    => '371',
   'DASDUGPE'    => '471',
   'DASDUGSP'    => '307',
   'DB2CONN'     => '308',
   'DB2CPKG'     => '227',
   'DB2CTASK'    => '339',
   'DB2LKCONF'   => '760',
   'DB2MSG'      => '2570',
   'DBCTHRDC'    => '640',
   'DBCTHRDD'    => '368',
   'DBCTHRDI'    => '124',
   'DBCTHRDS'    => '168',
   'DBM1STO'     => '360',
   'DEDB'        => '172',
   'DEPREGNS'    => '491',
   'DEVICES'     => '108',
   'DHCPSRV'     => '272',
   'DLIDEPRG'    => '676',
   'DNSDYNUPD'   => '264',
   'DNSMEMORY'   => '240',
   'DNSQUERY'    => '288',
   'DNSWINS'     => '248',
   'DNSZONET'    => '288',
   'DP_CI_EXCS'  => '112',
   'DP_CI_THDS'  => '104',
   'DP_DDF_CON'  => '96',
   'DP_DDF_STA'  => '364',
   'DP_IM_CONN'  => '72',
   'DP_IM_REG'   => '120',
   'DP_SRM_BPD'  => '353',
   'DP_SRM_BPM'  => '140',
   'DP_SRM_EDM'  => '584',
   'DP_SRM_EDX'  => '68',
   'DP_SRM_LOG'  => '672',
   'DP_SRM_LOX'  => '72',
   'DP_SRM_SUB'  => '858',
   'DP_SRM_SUX'  => '64',
   'DP_SRM_UTL'  => '144',
   'DP_SY_EXC'   => '624',
   'DP_TH_EXC'   => '1072',
   'DP_VOL_ACT'  => '244',
   'DPFILTER'    => '102',
   'DRDDC'       => '100',
   'DSNG_ATTR'   => '192',
   'DSNG_DETL'   => '846',
   'DSNG_DVOL'   => '315',
   'DSNG_SUMM'   => '416',
   'EDMPOOL'     => '612',
   'ENCTABLE'    => '164',
   'ENQUEUE'     => '339',
   'EXSUBSY1'    => '138',
   'EXSUBSYS'    => '345',
   'FCHANNEL'    => '296',
   'FFEXODS'     => '764',
   'FFEXRTS'     => '764',
   'FFEXSCHS'    => '764',
   'FFEXTRNSS'   => '764',
   'FILEINFO'    => '6232',                     # missing from load projections
   'FPREGNS'     => '161',
   'FPSYSTEM'    => '924',
   'FTPSTATS'    => '280',
   'FTPSVC'      => '216',
   'GB_POOL'     => '133',
   'GBP_CONN'    => '132',
   'GBP_STATS'   => '212',
   'GOAACTS'     => '240',
   'GOATHAS'     => '308',
   'GOATHVS'     => '234',
   'GOAVOLD'     => '230',
   'GOAVOLS'     => '242',
   'GOBJECTA'    => '128',
   'GOBJECTS'    => '132',
   'GOPHRSVC'    => '292',
   'HALDBPART'   => '116',
   'HALDBSUM'    => '214',
   'HLAADRS'     => '116',
   'HLALCPOL'    => '96',
   'HLALCPTH'    => '80',
   'HLALCSTR'    => '108',
   'HLALCSYS'    => '108',
   'HLALFILT'    => '69',
   'HLALXCFSY'   => '108',
   'HLHCHKS'     => '1180',
   'HLLXCFPT'    => '102',
   'HSM_ACTVTY'  => '59',
   'HSM_CDS'     => '118',
   'HSM_FUN_DA'  => '144',
   'HSM_REQS'    => '188',
   'HSM_STATUS'  => '234',
   'HTTPCNDX'    => '248',
   'HTTPSRVC'    => '328',
   'I3_MESSAGE'  => '124',
   'ICMPSTAT'    => '324',
   'ICTCBCPU'    => '120',
   'ICTLANDT'    => '152',
   'ICTLEXEV'    => '148',
   'ICTLIPDT'    => '148',
   'ICTLRTDT'    => '344',
   'ICTLTADT'    => '268',
   'ICTLTCSM'    => '268',
   'ICTLTDSM'    => '264',
   'ICTLTPSM'    => '268',
   'ICTLTTSM'    => '268',
   'ICTLTUSM'    => '267',
   'IISSTATS'    => '272',
   'IMS_SYS'     => '253',
   'IMSIO'       => '182',
   'INDEXSVC'    => '588',
   'INDEXSVCF'   => '556',
   'INTERACTN'   => '4116',
   'IP_IMS_STA'  => '184',
   'IPSTATS'     => '288',
   'IRLM'        => '200',
   'ISITSTSH'      => '624',
   'JNC747300'   => '136',
   'JOBOBJ'      => '644',
   'JOBOBJD'     => '672',
   'K06CSCRIP0' => '304',
   'K06CSCRIP1' => '391',
   'K06CSCRIP2' => '304',
   'K06K06CUS0' => '924',
   'K06LOGFILE' => '2824',
   'K06K06LOG0' => '600',
   'K06PERLEX0' => '364',
   'K06PERLEX1' => '344',
   'K06PERLEX2' => '1416',
   'K06PERLEX3' => '640',
   'K06PERLEX4' => '444',
   'K06PERLEX5' => '468',
   'K06PERLEX6' => '625',
   'K06POBJST'  => '324',
   'K06TEST' => '404',
   'K07K07ERL0' => '634',
   'K07K07ERS0'  => '176',
   'K07K07FSC0'  => '960',
   'K07K07LGS0'  => '1416',
   'K07K07LOG0'  => '668',
   'K07K07MAL0'  => '52',
   'K07K07MNT0'  => '1712',
   'K07K07NET0'  => '345',
   'K07K07NTP0'  => '334',
   'K07K07PAR0'  => '600',
   'K07K07SUB0'  => '288',
   'K07POBJST'   => '324',
   'K07PROCESS' => '468',
   'K07K07PRO0'  => '3979',
   'K07K07TRA0'  => '332',
   'K07K07URL0'  => '384',
   'K07K07USE0'  => '200',
   'K07K07CUS0' =>  '988',
   'K07K07MAI0' =>  '444',
   'K08K08CUS0' => '924',
   'K08K08FIL0' => '988',
   'K08K08FSA0' => '1968',
   'K08K08LOG0' => '1672',
   'K08K08MAI0' => '52',
   'K08K08MAI1' => '700',
   'K08K08NET0' => '357',
   'K08K08PAR0' => '856',
   'K08K08PROC' => '4299',
   'K08K08SCR0' => '1672',
   'K08K08TRA0' => '332',
   'K08K08URL0' => '896',
   'K08K08USE0' => '372',
   'K08CLUSTER' => '584',
   'K08POBJST'  => '324',
   'K08RESOURC' => '136',
   'K09K09CUS0' => '924',
   'K09K09FSC0' => '968',
   'K09K09SOL0' => '193',
   'K10K10FIL0' => '500',
   'K10MANAGED' => '628',
   'K12GSMAO10' => '436',
   'K12GSMAOR1' => '884',
   'K12GSMAOR2' => '820',
   'K12GSMAOR3' => '564',
   'K12GSMAOR4' => '884',
   'K12GSMAOR5' => '628',
   'K12GSMAOR6' => '628',
   'K12GSMAOR7' => '628',
   'K12GSMAOR8' => '500',
   'K12GSMAOR9' => '1204',
   'K12K12ORA2' => '712',
   'K12POBJST'  => '324',
   'K24EVENTLO'  => '2864',
   'K3ZEVTLOG'   => '2984',
   'K3ZNTDSAB'   => '244',
   'K3ZNTDSCNT'  => '848',
   'K3ZNTDSDAI'  => '1140',
   'K3ZNTDSDCA'  => '1836',
   'K3ZNTDSDCP'  => '420',
   'K3ZNTDSDFS'  => '384',
   'K3ZNTDSDHC'  => '348',
   'K3ZNTDSDNS'  => '584',
   'K3ZNTDSDRA'  => '844',
   'K3ZNTDSDS'   => '304',
   'K3ZNTDSFRS'  => '508',
   'K3ZNTDSFRT'  => '3280',
   'K3ZNTDSGPO'  => '484',
   'K3ZNTDSKCC'  => '316',
   'K3ZNTDSKDC'  => '228',
   'K3ZNTDSLDA'  => '96',
   'K3ZNTDSLDP'  => '272',
   'K3ZNTDSLFO'  => '344',
   'K3ZNTDSLSA'  => '228',
   'K3ZNTDSNSP'  => '232',
   'K3ZNTDSRDS'  => '476',
   'K3ZNTDSRLT'  => '936',
   'K3ZNTDSRPL'  => '1792',
   'K3ZNTDSSAM'  => '292',
   'K3ZNTDSSVC'  => '1340',
   'K3ZNTDSTRS'  => '552',
   'K3ZNTDSTTP'  => '640',
   'K3ZNTDSXDS'  => '232',
   'K3ZSYSRPL'   => '180',
   'K5DK5DSANP'  => '372',
   'K5ECSCRIPT'  => '188',
   'KA4ACCTJ'    => '194',
   'KA4ALERT'    => '161',
   'KA4APPN'     => '149',
   'KA4ASP'      => '124',
   'KA4ASYNC'    => '124',
   'KA4BSYNC'    => '140',
   'KA4CLUCRG'   => '280',
   'KA4CLUMRCS'  => '160',
   'KA4CLUNODE'  => '224',
   'KA4CTLD'     => '88',
   'KA4DBMBR'    => '177',
   'KA4DEVD'     => '134',
   'KA4DISK'     => '176',
   'KA4DISKI5'   => '144',
   'KA4DISTQ'    => '136',
   'KA4DTAQ'     => '96',
   'KA4ENET'     => '156',
   'KA4GPTFDTL'  => '145',
   'KA4GRPPTF'   => '232',
   'KA4HISTLOG'  => '908',
   'KA4IFSOBJ'   => '3232',
   'KA4INACJOB'  => '247',
   'KA4IOACBAT'  => '216',
   'KA4JOBLOG'   => '928',
   'KA4JOBQ'     => '108',
   'KA4LIND'     => '88',
   'KA4LPP'      => '132',
   'KA4MGTCNT'   => '1532',
   'KA4MISC'     => '368',
   'KA4MSG'      => '2304',
   'KA4NETA'     => '532',
   'KA4NETSRVR'  => '140',
   'KA4NWI'      => '92',
   'KA4NWS'      => '92',
   'KA4OBJ'      => '390',
   'KA4OUTPUTQ'  => '732',
   'KA4PFIOP'    => '211',
   'KA4PFJOB'    => '324',
   'KA4POOL'     => '144',
   'KA4PTF'      => '144',
   'KA4SBS'      => '124',
   'KA4SDLC'     => '188',
   'KA4SJAF'     => '138',
   'KA4SJAJ'     => '110',
   'KA4SJCA'     => '142',
   'KA4SJCP'     => '103',
   'KA4SJJD'     => '112',
   'KA4SJNA'     => '592',
   'KA4SJOW'     => '130',
   'KA4SJPA'     => '112',
   'KA4SJPS'     => '121',
   'KA4SJPW'     => '133',
   'KA4SJRJ'     => '112',
   'KA4SJRP'     => '112',
   'KA4SJSV'     => '592',
   'KA4SVACT'    => '385',
   'KA4SVAL'     => '145',
   'KA4SVALLOC'  => '100',
   'KA4SVDATIM'  => '132',
   'KA4SVDEV'    => '94',
   'KA4SVEDIT'   => '71',
   'KA4SVIPL'    => '82',
   'KA4SVOTHER'  => '164',
   'KA4SVPRB'    => '88',
   'KA4SVPRF'    => '147',
   'KA4SVSEC'    => '4030',
   'KA4SVSYCT1'  => '2228',
   'KA4SVSYCT2'  => '240',
   'KA4SVUSR'    => '587',
   'KA4SYSSTAT'  => '120',
   'KA4SYSTS'    => '188',
   'KA4TCPHOST'  => '1652',
   'KA4TCPINT'   => '280',
   'KA4TCPROUT'  => '346',
   'KA4TCPSRVC'  => '264',
   'KA4TKRNG'    => '156',
   'KA4USRGRP'   => '348',
   'KA4X25'      => '120',
   'KAGDYST'     => '504',     # kdy remote deploy
   'KAGREQT'     => '4096',    # kdy remote deploy
   'KBNCPUUSAG'  => '324',
   'KBNDATETIM'  => '952',
   'KBNDPCBATS'  => '368',
   'KBNDPCDS'    => '169',
   'KBNDPCENVS' => '600',
   'KBNDPCMEM' => '344',
   'KBNDPCUPTM' => '676',
   'KBNDPLOGNO'  => '1358',
   'KBNDPSDS' => '169',
   'KBNDPSPOS'   => '360',
   'KBNDPSTA17'  => '728',
   'KBNDPSTAT0'  => '480',
   'KBNDPSTAT2'  => '624',
   'KBNDPSTAT3'  => '480',
   'KBNDPSTAT4'  => '478',
   'KBNDPSTAT5'  => '368',
   'KBNDPSTAT6'  => '368',
   'KBNDPSTATU'  => '336',
   'KBNDSTATUS' => '1092',
   'KBNFILESYS'  => '416',
   'KBNFIRMWA0'  => '498',
   'KBNFIRMWAR'  => '544',
   'KBNHPLST'    => '132',
   'KBNHTTPCON'  => '804',
   'KBNLOGTARG'  => '724',
   'KBNMEMORYS'  => '380',
   'KBNMQCON' => '352',
   'KBNPOBJST'   => '360',
   'KBNSYSLOG0'  => '2021',
   'KBNSYSTEMU'  => '324',
   'KBNTCPSUMM'  => '392',
   'KBNTCPTABL'  => '684',
   'KD42IT'      => '1482',
   'KD42JT'      => '1614',
   'KD42MT'      => '1260',
   'KD43EM'      => '912',
   'KD43RP'      => '456',
   'KD43RQ'      => '400',
   'KD43RS'      => '420',
   'KD43SM'      => '118',
   'KD43SN'      => '132',
   'KD43SO'      => '516',
   'KD46AB'      => '96',
   'KD46AE'      => '764',
   'KD46BD'      => '664',
   'KD46BP'      => '384',
   'KD46BS'      => '1844',
   'KD47BA'      => '1080',
   'KD47BD'      => '720',
   'KD47BE'      => '490',
   'KD47BF'      => '2632',
   'KD47BG'      => '852',
   'KD47BN'      => '852',
   'KD47BP'      => '724',
   'KD9ALLENDP'  => '5904',
   'KD9ALLJOBS'  => '1928',
   'KD9BLDADSV'  => '6124',
   'KD9BLDASVG'  => '6164',
   'KD9CACHMEG'  => '3644',
   'KD9CACHMEM'  => '3612',
   'KD9CARD'     => '6600',
   'KD9CARDG'    => '6640',
   'KD9CHASSIG'  => '6420',
   'KD9CHASSIS'  => '6380',
   'KD9CHIP'     => '6200',
   'KD9CHIPG'    => '6240',
   'KD9DIREVT'   => '5328',
   'KD9DIREVTG'  => '4684',
   'KD9DISKDRG'  => '4172',
   'KD9DISKDRV'  => '4132',
   'KD9DISPCOG'  => '3576',
   'KD9DISPCON'  => '3536',
   'KD9DNSPEND'  => '3260',
   'KD9DNSPENG'  => '3300',
   'KD9DNSSETG'  => '4568',
   'KD9DNSSETN'  => '4528',
   'KD9DSKPARG'  => '3624',
   'KD9DSKPART'  => '3584',
   'KD9DSKTDRG'  => '3656',
   'KD9DSKTDRV'  => '3616',
   'KD9EPPOS'    => '360',
   'KD9ETHPORG'  => '3852',
   'KD9ETHPORT'  => '3812',
   'KD9EVTTYPS'  => '4144',
   'KD9FAN'      => '3512',
   'KD9FANG'     => '3552',
   'KD9FCPORT'   => '3816',
   'KD9FCPORTG'  => '3856',
   'KD9FILESYS'  => '6488',
   'KD9FILSYSG'  => '6528',
   'KD9FRU'      => '6332',
   'KD9FRUG'     => '6372',
   'KD9GHNTDEV'  => '6124',
   'KD9GNTDEVG'  => '6164',
   'KD9GRPENDP'  => '5384',
   'KD9GRPOS'    => '360',
   'KD9HDMNCNS'  => '6252',
   'KD9HMNCNSG'  => '6292',
   'KD9IDECONG'  => '3564',
   'KD9IDECONT'  => '3524',
   'KD9INV1'     => '952',
   'KD9INV1G'    => '432',
   'KD9IPPREND'  => '2792',
   'KD9IPPRENG'  => '2832',
   'KD9JOBS'     => '2448',
   'KD9JOBSG'    => '1928',
   'KD9KEYBORD'  => '3676',
   'KD9KEYBORG'  => '3716',
   'KD9LANEND'   => '2900',
   'KD9LANENDG'  => '2940',
   'KD9LOCATN'   => '5664',
   'KD9LOCATNG'  => '5704',
   'KD9LOGMOD'   => '3512',
   'KD9LOGMODG'  => '3552',
   'KD9LOGVOL'   => '3572',
   'KD9LOGVOLG'  => '3612',
   'KD9MEMORY'   => '3588',
   'KD9MEMORYG'  => '3628',
   'KD9MNGCONT'  => '6124',
   'KD9MNGCTRG'  => '6164',
   'KD9OPERSYS'  => '4612',
   'KD9OPRSYSG'  => '4652',
   'KD9OPTDRIV'  => '3616',
   'KD9OPTDRVG'  => '3656',
   'KD9PASSTMD'  => '6152',
   'KD9PASTMDG'  => '6192',
   'KD9PCIBRGG'  => '3760',
   'KD9PCIBRIG'  => '3720',
   'KD9PCIDEV'   => '3752',
   'KD9PCIDEVG'  => '3808',
   'KD9PHYFRAM'  => '6364',
   'KD9PHYFRMG'  => '6404',
   'KD9PHYLINK'  => '6200',
   'KD9PHYLNKG'  => '6240',
   'KD9PHYMEMG'  => '6404',
   'KD9PHYPACK'  => '6332',
   'KD9PHYPCKG'  => '6372',
   'KD9PHYPRT'   => '6212',
   'KD9PHYPRTG'  => '6252',
   'KD9PHYSCNG'  => '6248',
   'KD9PHYSCON'  => '6208',
   'KD9PHYSMEM'  => '6364',
   'KD9PHYSVLG'  => '3612',
   'KD9PHYSVOL'  => '3572',
   'KD9PLLCNTG'  => '3568',
   'KD9PLLCONT'  => '3528',
   'KD9POBJST'   => '360',
   'KD9POINTDG'  => '3568',
   'KD9POINTDV'  => '3528',
   'KD9PORTCNG'  => '3568',
   'KD9PORTCON'  => '3528',
   'KD9PRCSSRG'  => '4396',
   'KD9PRINTER'  => '3756',
   'KD9PRINTRG'  => '3796',
   'KD9PROCSSR'  => '4356',
   'KD9RAIDCNG'  => '6036',
   'KD9RAIDCON'  => '5996',
   'KD9RSACCPT'  => '5216',
   'KD9RSACPG'   => '5256',
   'KD9SASPORT'  => '3808',
   'KD9SASPRTG'  => '3848',
   'KD9SASTSET'  => '3176',
   'KD9SCSIPE'   => '2360',
   'KD9SCSIPEG'  => '2400',
   'KD9SDEVCND'  => '564',
   'KD9SDEVDET'  => '2104',
   'KD9SDEVDTI'  => '5428',
   'KD9SDEVTS'   => '5172',
   'KD9SERCON'   => '3528',
   'KD9SERCONG'  => '3568',
   'KD9SERVER'   => '6516',
   'KD9SERVERG'  => '6548',
   'KD9SLOT'     => '7168',
   'KD9SLOTG'    => '7208',
   'KD9SNMPTT'   => '4884',
   'KD9SNMPTTG'  => '4924',
   'KD9STGSSG'   => '6680',
   'KD9STORSUB'  => '6640',
   'KD9STORVLG'  => '3612',
   'KD9STORVOL'  => '3572',
   'KD9SWITCH'   => '6324',
   'KD9SWITCHG'  => '6364',
   'KD9SYSASTG'  => '3216',
   'KD9SYSCHAS'  => '7048',
   'KD9SYSCHSG'  => '7088',
   'KD9SYSDISC'  => '1412',
   'KD9SYSENDP'  => '5904',
   'KD9THPLST'   => '132',
   'KD9TIMZNS'   => '2680',
   'KD9TIMZNSG'  => '2720',
   'KD9USBCON'   => '3592',
   'KD9USBCONG'  => '3632',
   'KD9VIDHEAD'  => '3656',
   'KD9VIDHEDG'  => '3712',
   'KDOCFSTAT'   => '397',
   'KDOCICTRAN'  => '238',
   'KDODB2TRAN'  => '190',
   'KDODEVSTAT'  => '248',
   'KDOIMSTRAN'  => '270',
   'KDOJOBADDR'  => '156',
   'KDOMVSLPAR'  => '138',
   'KDOPOBJST'   => '260',
   'KDOSYSSTAT'  => '174',
   'KDOTCPCONN'  => '196',
   'KDOVOLINFO'  => '178',
   'KDOWLMSTAT'  => '308',
   'KDOZLINUX'   => '222',
   'KDP_CFG'     => '181',
   'KE1ACDS'     => '169',
   'KE1ACPOS'    => '360',
   'KE1AHUA'     => '1196',
   'KE1AHUB'     => '1180',
   'KE1AHUDS'    => '169',
   'KE1AHUPOS'   => '360',
   'KE1AHUS'     => '1410',
   'KE1BLRA'     => '1196',
   'KE1BLRB'     => '1180',
   'KE1BLRDS'    => '169',
   'KE1BLRPOS'   => '360',
   'KE1BLRS'     => '700',
   'KE1CDUA'     => '1196',
   'KE1CDUB'     => '1180',
   'KE1CDUDS'    => '169',
   'KE1CDUPOS'   => '360',
   'KE1CDUS'     => '294',
   'KE1CHPA'     => '1196',
   'KE1CHPB'     => '1180',
   'KE1CHPDS'    => '169',
   'KE1CHPPOS'   => '360',
   'KE1CHPS'     => '338',
   'KE1CHRS'     => '616',
   'KE1CRACA'    => '1196',
   'KE1CRACB'    => '1180',
   'KE1CRACS'    => '572',
   'KE1FMDS'     => '169',
   'KE1FMPOS'    => '360',
   'KE1FMS'      => '262',
   'KE1FUELMTA'  => '1196',
   'KE1FUELMTB'  => '1180',
   'KE1GENA'     => '1196',
   'KE1GENB'     => '1180',
   'KE1GENDS'    => '169',
   'KE1GENPOS'   => '360',
   'KE1GENS'     => '566',
   'KE1HXUA'     => '1196',
   'KE1HXUB'     => '1180',
   'KE1HXUDS'    => '169',
   'KE1HXUPOS'   => '360',
   'KE1HXUS'     => '262',
   'KE1MTRA'     => '1314',
   'KE1MTRB'     => '1180',
   'KE1MTRDS'    => '169',
   'KE1MTRPOS'   => '360',
   'KE1MTRS'     => '326',
   'KE1OTHA'     => '1196',
   'KE1OTHB'     => '1180',
   'KE1OTHDS'    => '169',
   'KE1OTHPOS'   => '360',
   'KE1PDUA'     => '1196',
   'KE1PDUB'     => '1180',
   'KE1PDUBS'    => '674',
   'KE1PDUDS'    => '169',
   'KE1PDUPOS'   => '360',
   'KE1PDUPS'    => '524',
   'KE1PDUS'     => '278',
   'KE1POBJST'   => '360',
   'KE1RPTAC'    => '2084',
   'KE1RPTAHU'   => '2866',
   'KE1RPTBKR'   => '566',
   'KE1RPTBLR'   => '2274',
   'KE1RPTCDU'   => '2012',
   'KE1RPTCHP'   => '2016',
   'KE1RPTCHR'   => '2298',
   'KE1RPTFM'    => '1992',
   'KE1RPTGEN'   => '2000',
   'KE1RPTHXU'   => '2004',
   'KE1RPTINFO'  => '366',
   'KE1RPTMTR'   => '1996',
   'KE1RPTPDU'   => '1984',
   'KE1RPTPNL'   => '364',
   'KE1RPTSNS'   => '2008',
   'KE1RPTUPS'   => '2032',
   'KE1SNSA'     => '1196',
   'KE1SNSB'     => '1180',
   'KE1SNSDS'    => '169',
   'KE1SNSPOS'   => '360',
   'KE1SNSS'     => '800',
   'KE1THPLST'   => '132',
   'KE1UPSA'     => '1196',
   'KE1UPSB'     => '1180',
   'KE1UPSDS'    => '169',
   'KE1UPSPOS'   => '360',
   'KE1UPSS'     => '570',
   'KE4ACDS'     => '169',
   'KE4ACPOS'    => '360',
   'KE4AHUA'     => '1046',
   'KE4AHUB'     => '1030',
   'KE4AHUDS'    => '169',
   'KE4AHUPOS'   => '360',
   'KE4AHUS'     => '1394',
   'KE4BLRA'     => '1046',
   'KE4BLRB'     => '1030',
   'KE4BLRDS'    => '169',
   'KE4BLRPOS'   => '360',
   'KE4BLRS'     => '700',
   'KE4CDUA'     => '1046',
   'KE4CDUB'     => '1030',
   'KE4CDUDS'    => '169',
   'KE4CDUPOS'   => '360',
   'KE4CDUS'     => '294',
   'KE4CHPA'     => '1046',
   'KE4CHPB'     => '1030',
   'KE4CHPDS'    => '169',
   'KE4CHPPOS'   => '360',
   'KE4CHPS'     => '338',
   'KE4CHRA'     => '1046',
   'KE4CHRB'     => '1030',
   'KE4CHRDS'    => '169',
   'KE4CHRPOS'   => '360',
   'KE4CHRS'     => '720',
   'KE4CRACA'    => '1046',
   'KE4CRACB'    => '1030',
   'KE4CRACS'    => '556',
   'KE4FMA'      => '1046',
   'KE4FMB'      => '1030',
   'KE4FMDS'     => '169',
   'KE4FMPOS'    => '360',
   'KE4FMS'      => '262',
   'KE4GENA'     => '1046',
   'KE4GENB'     => '1030',
   'KE4GENDS'    => '169',
   'KE4GENPOS'   => '360',
   'KE4GENS'     => '582',
   'KE4HXUA'     => '1046',
   'KE4HXUB'     => '1030',
   'KE4HXUDS'    => '169',
   'KE4HXUPOS'   => '360',
   'KE4HXUS'     => '262',
   'KE4MTRA'     => '1046',
   'KE4MTRB'     => '1030',
   'KE4MTRDS'    => '169',
   'KE4MTRPOS'   => '360',
   'KE4MTRS'     => '326',
   'KE4OTHA'     => '1046',
   'KE4OTHB'     => '1030',
   'KE4OTHDS'    => '169',
   'KE4OTHPOS'   => '360',
   'KE4PDUA'     => '1046',
   'KE4PDUB'     => '1030',
   'KE4PDUBS'    => '674',
   'KE4PDUDS'    => '169',
   'KE4PDUPOS'   => '360',
   'KE4PDUPS'    => '524',
   'KE4PDUS'     => '278',
   'KE4POBJST'   => '360',
   'KE4RPTAC'    => '2234',
   'KE4RPTAC2'   => '2234',
   'KE4RPTAHU'   => '2866',
   'KE4RPTBKR'   => '2336',
   'KE4RPTBLR'   => '2274',
   'KE4RPTCDU'   => '2012',
   'KE4RPTCHP'   => '2166',
   'KE4RPTCHR'   => '2448',
   'KE4RPTFM'    => '1992',
   'KE4RPTGEN'   => '2150',
   'KE4RPTHXU'   => '2004',
   'KE4RPTINFO'  => '366',
   'KE4RPTMTR'   => '2146',
   'KE4RPTPDU'   => '2134',
   'KE4RPTPNL'   => '2134',
   'KE4RPTSNS'   => '2158',
   'KE4RPTUPS'   => '2182',
   'KE4SNSA'     => '1046',
   'KE4SNSB'     => '1030',
   'KE4SNSDS'    => '169',
   'KE4SNSPOS'   => '360',
   'KE4SNSS'     => '800',
   'KE4THPLST'   => '132',
   'KE4UPSA'     => '1046',
   'KE4UPSB'     => '1030',
   'KE4UPSDS'    => '169',
   'KE4UPSPOS'   => '360',
   'KE4UPSS'     => '570',
   'KE6ACDS'     => '169',
   'KE6ACPOS'    => '360',
   'KE6AHUA'     => '1334',
   'KE6AHUB'     => '1318',
   'KE6AHUDS'    => '169',
   'KE6AHUPOS'   => '360',
   'KE6AHUS'     => '1394',
   'KE6BLRA'     => '1334',
   'KE6BLRB'     => '1318',
   'KE6BLRDS'    => '169',
   'KE6BLRPOS'   => '360',
   'KE6BLRS'     => '700',
   'KE6CDUA'     => '1334',
   'KE6CDUB'     => '1318',
   'KE6CDUDS'    => '169',
   'KE6CDUPOS'   => '360',
   'KE6CDUS'     => '294',
   'KE6CHPA'     => '1334',
   'KE6CHPB'     => '1318',
   'KE6CHPDS'    => '169',
   'KE6CHPPOS'   => '360',
   'KE6CHPS'     => '338',
   'KE6CHRA'     => '1334',
   'KE6CHRB'     => '1318',
   'KE6CHRDS'    => '169',
   'KE6CHRPOS'   => '360',
   'KE6CHRS'     => '3226',
   'KE6CRACA'    => '1334',
   'KE6CRACB'    => '1318',
   'KE6CRACS'    => '2732',
   'KE6FMA'      => '1334',
   'KE6FMB'      => '1318',
   'KE6FMDS'     => '169',
   'KE6FMPOS'    => '360',
   'KE6FMS'      => '262',
   'KE6GENA'     => '1334',
   'KE6GENB'     => '1318',
   'KE6GENDS'    => '169',
   'KE6GENPOS'   => '360',
   'KE6GENS'     => '2780',
   'KE6HXUA'     => '1334',
   'KE6HXUB'     => '1318',
   'KE6HXUDS'    => '169',
   'KE6HXUPOS'   => '360',
   'KE6HXUS'     => '262',
   'KE6KE6WOUT'  => '1122',
   'KE6MTRA'     => '1334',
   'KE6MTRB'     => '1318',
   'KE6MTRDS'    => '169',
   'KE6MTRPOS'   => '360',
   'KE6MTRS'     => '326',
   'KE6OTHA'     => '1334',
   'KE6OTHB'     => '1318',
   'KE6OTHDS'    => '169',
   'KE6OTHPOS'   => '360',
   'KE6PDUA'     => '1334',
   'KE6PDUB'     => '1318',
   'KE6PDUBS'    => '674',
   'KE6PDUDS'    => '169',
   'KE6PDUPOS'   => '360',
   'KE6PDUPS'    => '524',
   'KE6PDUS'     => '2780',
   'KE6POBJST'   => '360',
   'KE6RPTAC'    => '2084',
   'KE6RPTAHU'   => '2866',
   'KE6RPTBKR'   => '582',
   'KE6RPTBLR'   => '2274',
   'KE6RPTCDU'   => '2012',
   'KE6RPTCHP'   => '2016',
   'KE6RPTCHR'   => '2548',
   'KE6RPTFM'    => '1992',
   'KE6RPTGEN'   => '1996',
   'KE6RPTHXU'   => '2004',
   'KE6RPTINFO'  => '366',
   'KE6RPTMTR'   => '1996',
   'KE6RPTPDU'   => '1984',
   'KE6RPTPNL'   => '364',
   'KE6RPTSNS'   => '2008',
   'KE6RPTUPS'   => '2032',
   'KE6SNSA'     => '3290',
   'KE6SNSDS'    => '169',
   'KE6SNSPOS'   => '360',
   'KE6THPLST'   => '132',
   'KE6UPSA'     => '1334',
   'KE6UPSB'     => '1318',
   'KE6UPSDS'    => '169',
   'KE6UPSPOS'   => '360',
   'KE6UPSS'     => '2844',
   'KE7AIRDS'    => '169',
   'KE7AIRFMS8'  => '372',
   'KE7AIRFMSY'  => '312',
   'KE7AIRID'    => '4006',
   'KE7AIRIR11'  => '1934',
   'KE7AIRIR14'  => '204',
   'KE7AIRIR20'  => '1938',
   'KE7AIRIR23'  => '208',
   'KE7AIRIR26'  => '152',
   'KE7AIRIRG6'  => '1866',
   'KE7AIRIRM3'  => '112',
   'KE7AIRIRM6'  => '1990',
   'KE7AIRIRR3'  => '1882',
   'KE7AIRIRR6'  => '160',
   'KE7AIRIRS0'  => '1862',
   'KE7AIRIRS3'  => '256',
   'KE7AIRPOS'   => '360',
   'KE7ARUDS'    => '169',
   'KE7ARUPOS'   => '360',
   'KE7EEMDS'    => '169',
   'KE7EEMPOS'   => '360',
   'KE7EMCONF0'  => '192',
   'KE7EMCONF1'  => '56',
   'KE7EMCONFI'  => '256',
   'KE7EMIDENT'  => '1702',
   'KE7EMSTAT0'  => '120',
   'KE7EMSTAT1'  => '60',
   'KE7EMSTATU'  => '164',
   'KE7IEMCON0'  => '192',
   'KE7IEMCON1'  => '56',
   'KE7IEMCONF'  => '256',
   'KE7IEMDS'    => '169',
   'KE7IEMIDEN'  => '1702',
   'KE7IEMPOS'   => '360',
   'KE7IEMSTA0'  => '120',
   'KE7IEMSTA1'  => '120',
   'KE7IEMSTA2'  => '60',
   'KE7IEMSTAT'  => '228',
   'KE7POBJST'   => '360',
   'KE7RARUCON'  => '128',
   'KE7RARUFAN'  => '164',
   'KE7RARUIDE'  => '116',
   'KE7RARUPOW'  => '64',
   'KE7RARUSE0'  => '236',
   'KE7RARUSEN'  => '60',
   'KE7RARUST0'  => '56',
   'KE7RARUSTA'  => '224',
   'KE7RPDDS'    => '169',
   'KE7RPDPOS'   => '360',
   'KE7RPDUIDE'  => '2022',
   'KE7RPDULO0'  => '60',
   'KE7RPDULO1'  => '1662',
   'KE7RPDULO2'  => '68',
   'KE7RPDULO3'  => '80',
   'KE7RPDULO4'  => '68',
   'KE7RPDULOA'  => '60',
   'KE7RPDUOU3'  => '132',
   'KE7RPDUOU5'  => '148',
   'KE7RPDUOUT'  => '72',
   'KE7RPDUST0'  => '60',
   'KE7RPDUST1'  => '60',
   'KE7RPDUSTA'  => '60',
   'KE7RPTINFO'  => '366',
   'KE7THPLST'   => '132',
   'KE7UPSADV0'  => '72',
   'KE7UPSADV2'  => '72',
   'KE7UPSADVB'  => '60',
   'KE7UPSADVI'  => '2022',
   'KE7UPSADVO'  => '1666',
   'KE7UPSBAS0'  => '1858',
   'KE7UPSBAS6'  => '432',
   'KE7UPSDS'    => '169',
   'KE7UPSPHA0'  => '144',
   'KE7UPSPHA1'  => '1718',
   'KE7UPSPHA3'  => '76',
   'KE7UPSPHA4'  => '1746',
   'KE7UPSPOS'   => '360',
   'KE7XPDDS'    => '169',
   'KE7XPDPOS'   => '360',
   'KE7XPDUBR0'  => '52',
   'KE7XPDUBRA'  => '216',
   'KE7XPDUDEV'  => '60',
   'KE7XPDUIDE'  => '2150',
   'KE7XPDUMA0'  => '56',
   'KE7XPDUMAI'  => '84',
   'KE7XPDUSY0'  => '1750',
   'KE7XPDUSY1'  => '56',
   'KE7XPDUSYS'  => '148',
   'KE8GTACTA'   => '634',
   'KE8GTALRM'   => '52',
   'KE8GTDEVCO'  => '2757',
   'KE8GTIDDM'   => '1431',
   'KE8GTIDEM'   => '2742',
   'KE8GTIDMAM'  => '1415',
   'KE8GTIDMPQ'  => '1411',
   'KE8GTIDPCM'  => '1413',
   'KE8GTIDPDI'  => '1557',
   'KE8GTIDPDO'  => '1557',
   'KE8GTIDPPH'  => '1351',
   'KE8GTIDPSN'  => '1434',
   'KE8GTIDPSS'  => '1374',
   'KE8GTIDRTM'  => '1363',
   'KE8GTIDRTP'  => '1363',
   'KE8GTSYS'    => '1196',
   'KE8GTWPOS'   => '360',
   'KE8MGDGTW'   => '169',
   'KE8MGDMTR'   => '169',
   'KE8MGDPDU'   => '169',
   'KE8MGDUPS'   => '169',
   'KE8MTRACAI'  => '634',
   'KE8MTRACTA'  => '698',
   'KE8MTRALRM'  => '52',
   'KE8MTRID'    => '432',
   'KE8MTRPHYS'  => '3069',
   'KE8MTRPOS'   => '360',
   'KE8MTRPOWE'  => '164',
   'KE8MTRPQSA'  => '95',
   'KE8MTRSYS'   => '878',
   'KE8MTRURI'   => '112',
   'KE8PCDMEAS'  => '134',
   'KE8PCDPHAS'  => '72',
   'KE8PDUACAI'  => '634',
   'KE8PDUACTA'  => '698',
   'KE8PDUALRM'  => '52',
   'KE8PDUBMT'   => '64',
   'KE8PDUBPMT'  => '1670',
   'KE8PDUBRT'   => '95',
   'KE8PDUCON'   => '123',
   'KE8PDUENV'   => '76',
   'KE8PDUID'    => '432',
   'KE8PDUINP'   => '1693',
   'KE8PDUINPT'  => '64',
   'KE8PDUIO'    => '495',
   'KE8PDUIOT'   => '1756',
   'KE8PDUNAME'  => '64',
   'KE8PDUOUT'   => '111',
   'KE8PDUOUTT'  => '64',
   'KE8PDUPHYS'  => '1479',
   'KE8PDUPMT'   => '76',
   'KE8PDUPOS'   => '360',
   'KE8PDUPPMT'  => '68',
   'KE8PDUPRT'   => '99',
   'KE8PDUSYS'   => '878',
   'KE8PDUURI'   => '112',
   'KE8PDUWBM2'  => '2054',
   'KE8PDUWBMT'  => '448',
   'KE8PDUWBRT'  => '479',
   'KE8PDUWENV'  => '460',
   'KE8PDUWINP'  => '2077',
   'KE8PDUWINT'  => '448',
   'KE8PDUWNAM'  => '448',
   'KE8PDUWOTT'  => '448',
   'KE8PDUWOUT'  => '80',
   'KE8PDUWPM2'  => '452',
   'KE8PDUWPMT'  => '460',
   'KE8PDUWPRT'  => '483',
   'KE8POBJST'   => '360',
   'KE8PWRMET0'  => '84',
   'KE8PWRMET1'  => '136',
   'KE8PWRMET2'  => '1718',
   'KE8PWRMET3'  => '152',
   'KE8PWRMETE'  => '84',
   'KE8RPTGMET'  => '2969',
   'KE8RPTINFO'  => '366',
   'KE8THPLST'   => '132',
   'KE8UPSACAI'  => '634',
   'KE8UPSACTA'  => '698',
   'KE8UPSALRM'  => '52',
   'KE8UPSBAT'   => '1678',
   'KE8UPSBYP'   => '56',
   'KE8UPSBYPT'  => '56',
   'KE8UPSCFG'   => '110',
   'KE8UPSCON'   => '123',
   'KE8UPSENV'   => '92',
   'KE8UPSID'    => '173',
   'KE8UPSIDE'   => '236',
   'KE8UPSIDU'   => '300',
   'KE8UPSINP'   => '68',
   'KE8UPSINPT'  => '1658',
   'KE8UPSIO'    => '1674',
   'KE8UPSIOT'   => '1678',
   'KE8UPSOUT'   => '1654',
   'KE8UPSOUTT'  => '68',
   'KE8UPSPHYS'  => '1479',
   'KE8UPSPOS'   => '360',
   'KE8UPSRECT'  => '72',
   'KE8UPSSYS'   => '878',
   'KE8UPSTES'   => '60',
   'KE8UPSTOP'   => '64',
   'KE8UPSURI'   => '112',
   'KE8UPSWBYP'  => '181',
   'KE8UPSWBYT'  => '181',
   'KE8UPSWCFG'  => '235',
   'KE8UPSWENV'  => '217',
   'KE8UPSWINP'  => '193',
   'KE8UPSWINT'  => '1783',
   'KE8UPSWOTT'  => '193',
   'KE8UPSWOUT'  => '1779',
   'KE8UPSWTOP'  => '189',
   'KE9ACPOS'    => '360',
   'KE9ALL'      => '152',
   'KE9ALLBC'    => '3770',
   'KE9ALLCRAC'  => '3168',
   'KE9ALLDAG'   => '169',
   'KE9ALLPDU'   => '1532',
   'KE9ALLPDU2'  => '2844',
   'KE9ALLPOS'   => '360',
   'KE9ALLRK1'   => '2942',
   'KE9ALLRS1'   => '3344',
   'KE9ALLSNNC'  => '2298',
   'KE9ALLSNS'   => '496',
   'KE9ALLSNSC'  => '2548',
   'KE9ALLSZ1'   => '2804',
   'KE9ALLSZ2'   => '1088',
   'KE9ALLUPS'   => '3388',
   'KE9ALLZEN1'  => '2456',
   'KE9BC'       => '3770',
   'KE9BCE'      => '1138',
   'KE9BCPOS'    => '360',
   'KE9BLDAG'    => '169',
   'KE9CRACDAG'  => '169',
   'KE9CRACDAT'  => '3168',
   'KE9PDU'      => '1532',
   'KE9PDU2'     => '2844',
   'KE9PDUDAG'   => '169',
   'KE9PDUDEV'   => '1101',
   'KE9PDUGRP'   => '722',
   'KE9PDUOUTL'  => '1262',
   'KE9PDUPOS'   => '360',
   'KE9PDUSENS'  => '680',
   'KE9POBJST'   => '360',
   'KE9RADAG'    => '169',
   'KE9RK1'      => '2942',
   'KE9RKDAG'    => '169',
   'KE9RKPOS'    => '360',
   'KE9RPTINFO'  => '366',
   'KE9RS1'      => '3344',
   'KE9RSPOS'    => '360',
   'KE9SNNC'     => '2298',
   'KE9SNS'      => '496',
   'KE9SNSC'     => '2548',
   'KE9SNSDAG'   => '169',
   'KE9SNSPOS'   => '360',
   'KE9SYDAG'    => '169',
   'KE9SZ1'      => '2804',
   'KE9SZ2'      => '1088',
   'KE9SZPOS'    => '360',
   'KE9THPLST'   => '132',
   'KE9UPSDAG'   => '169',
   'KE9UPSDAT'   => '3388',
   'KE9UPSPOS'   => '360',
   'KE9UPSSNS'   => '680',
   'KE9ZENPOS'   => '360',
   'KE9ZENT1'    => '2456',
   'KE9ZENTDAG'  => '169',
   'KEXSMTP'     => '668',
   'KGBAVAIL'    => '3244',
   'KGBDAGNT'    => '164',
   'KGBDCAL'     => '172',
   'KGBDCAL64'   => '196',
   'KGBDCFD'     => '748',
   'KGBDCMD'     => '316',
   'KGBDDB'      => '220',
   'KGBDDB64'    => '292',
   'KGBDDBW'     => '292',
   'KGBDGU'      => '348',
   'KGBDICM'     => '468',
   'KGBDICM64'   => '580',
   'KGBDIMAP'    => '184',
   'KGBDIMAP64'  => '220',
   'KGBDLDAP'    => '308',
   'KGBDLDAP64'  => '368',
   'KGBDMAIL'    => '236',
   'KGBDMAIL64'  => '336',
   'KGBDMBD'     => '268',
   'KGBDMBD64'   => '264',
   'KGBDNETT'    => '168',
   'KGBDNETT64'  => '204',
   'KGBDREP'     => '168',
   'KGBDREP64'   => '188',
   'KGBDREPC'    => '204',
   'KGBDREPC64'  => '256',
   'KGBDRPL'     => '756',
   'KGBDSMTP'    => '172',
   'KGBDSMTP64'  => '180',
   'KGBDSRV'     => '584',
   'KGBDSRV64'   => '636',
   'KGBDSRVC'    => '200',
   'KGBDTASK'    => '448',
   'KGBDWR'      => '1064',
   'KGBIMDOM'    => '356',
   'KGBIMINC'    => '364',
   'KGBIMOUT'    => '356',
   'KGBIMSIZ'    => '360',
   'KGBIREP'     => '384',
   'KGBIREPD'    => '356',
   'KGBISERV'    => '520',
   'KGBIVPERF'   => '364',
   'KGBKGBLOG0'  => '816',
   'KGBDMAIL'    => '236',
   'KGBPOBJST'   => '260',
   'KHDCONF'     => '264',
   'KHDDBINFO'   => '1284',
   'KHDLASTERR'  => '1579',
   'KHDLOADST'   => '136',
   'KHDNODELST'  => '140',
   'KHDRGADLST'  => '268',
   'KHDRPCS'     => '92',
   'KHDTEMSLST'  => '80',
   'KHDWORKQ'    => '132',
   'KHTAWEBSR'   => '1100',
   'KHTAWEBST'   => '1052',
   'KHTEVNT'     => '588',
   'KHTSWEBSR'   => '2940',
   'KHTSWEBST'   => '1344',
   'KHTWSRS'     => '1000',
   'KHVAVAIL'    => '3244',
   'KHVDIRECTO'  => '145',
   'KHVEVTLOG'   => '2216',
   'KHVGETDIS0'  => '280',
   'KHVGETMEM0'  => '260',
   'KHVGETPRO0'  => '208',
   'KHVGETVIR0'  => '860',
   'KHVHVSDISK'  => '192',
   'KHVHYLPROC'  => '224',
   'KHVHYPART'   => '200',
   'KHVHYPERV'   => '80',
   'KHVHYPERVI'  => '1094',
   'KHVHYPVRST'  => '188',
   'KHVHYRPART'  => '180',
   'KHVHYRPROC'  => '228',
   'KHVHYRPROM'  => '1172',
   'KHVHYVIDP'   => '368',
   'KHVHYVPROC'  => '336',
   'KHVHYVPROM'  => '1140',
   'KHVLEGNWAD'  => '220',
   'KHVMSVMVI4'  => '214',
   'KHVMSVMVI5'  => '268',
   'KHVNVVMIGR'  => '468',
   'KHVPOBJST'   => '360',
   'KHVTASKMD'   => '240',
   'KHVTASKMDR'  => '816',
   'KHVTHPLST'   => '132',
   'KHVVIDECON'  => '212',
   'KHVVIRNWAD'  => '340',
   'KHVVIRSWIT'  => '304',
   'KHVVIRSWPO'  => '365',
   'KHVVMBUS'    => '72',
   'KHVVMHESUM'  => '56',
   'KHVVMIOAPI'  => '152',
   'KHVVMMODF'   => '610',
   'KHVVMSUMMA'  => '120',
   'KHVVSTORDV'  => '412',
   'KIC1034900'  => '944',
   'KIC1675900'  => '944',
   'KIC345600'   => '1020',
   'KIC4091900'  => '1196',
   'KIMALARMS'   => '590',
   'KIMAUDINFO'  => '336',
   'KIMAUDMASK'  => '160',
   'KIMAVAIL'    => '3244',
   'KIMBARALOG'  => '356',
   'KIMBUFPOOL'  => '416',
   'KIMCDRERR'   => '1349',
   'KIMCDRLAT'   => '376',
   'KIMCDRPART'  => '1733',
   'KIMCDRPROG'  => '492',
   'KIMCDRQ'     => '312',
   'KIMCDRRCVS'  => '408',
   'KIMCDRREPL'  => '495',
   'KIMCDRRQM'   => '360',
   'KIMCDRS'     => '228',
   'KIMCHFREE'   => '96',
   'KIMCHKPT'    => '264',
   'KIMCHUNKS'   => '480',
   'KIMDATABAS'  => '376',
   'KIMDBSPACE'  => '396',
   'KIMEXTSPAC'  => '472',
   'KIMGENERAL'  => '243',
   'KIMHA_LAT'   => '208',
   'KIMHA_TYPE'  => '180',
   'KIMHA_WORK'  => '220',
   'KIMHANODES'  => '184',
   'KIMINDEXES'  => '812',
   'KIMIPL'      => '72',
   'KIMLATENCY'  => '80',
   'KIMLLOGBUF'  => '144',
   'KIMLLOGFIL'  => '148',
   'KIMLLOGSUM'  => '152',
   'KIMLOCKS'    => '413',
   'KIMLRUS'     => '104',
   'KIMMACHINE'  => '744',
   'KIMMEMPOOL'  => '104',
   'KIMMGMGATE'  => '76',
   'KIMMGMINFO'  => '312',
   'KIMMGMQURY'  => '130',
   'KIMNETCLNT'  => '166',
   'KIMNETGLOB'  => '304',
   'KIMNETWORK'  => '326',
   'KIMONCFG'    => '1723',
   'KIMONLILOG'  => '356',
   'KIMPLOG'     => '136',
   'KIMPOBJST'   => '260',
   'KIMPROF_D'   => '368',
   'KIMPROF_DT'  => '368',
   'KIMPROFILE'  => '368',
   'KIMRSSLOG'   => '248',
   'KIMSESENV'   => '696',
   'KIMSESSION'  => '1848',
   'KIMSHMSEGS'  => '128',
   'KIMSMX'      => '364',
   'KIMSMXSES'   => '244',
   'KIMSQLHOST'  => '583',
   'KIMSQLTRC'   => '1732',
   'KIMSQLTRIN'  => '114',
   'KIMSQLTRIT'  => '116',
   'KIMSRCRSS'   => '268',
   'KIMSRCSDS'   => '328',
   'KIMSRVENV'   => '688',
   'KIMTABLES'   => '551',
   'KIMTHREADS'  => '200',
   'KIMTRANSAC'  => '251',
   'KIMTRGRSS'   => '228',
   'KIMTRGSDS'   => '1556',
   'KIMVPS'      => '128',
   'KIMWAITSTA'  => '139',
   'KINAGT'      => '797',    # kdy remote deploy
   'KIP_LRTENO'  => '148',
   'KIP_LRTETE'  => '116',
   'KIP_LRTEXC'  => '438',
   'KIP_LRTG02'  => '442',
   'KIP_LRTI02'  => '168',
   'KIP_LRTISU'  => '168',
   'KIP_LRTSSU'  => '144',
   'KIP_LRTTMO'  => '144',
   'KIP_LRTXMO'  => '186',
   'KIP_MQ_ST'   => '430',
   'KIP_MSC_S'   => '164',
   'KIP_RTISU'   => '168',
   'KIP_RTSSU'   => '220',
   'KIPDEXDL'    => '868',
   'KIPDEXSU'    => '428',
   'KIPLOCKCNF'  => '428',
   'KIPVSAM'     => '274',
   'KISDHCP'     => '724',
   'KISDIAL'     => '804',
   'KISDNS'      => '772',
   'KISFTP'      => '988',
   'KISHSTATS'   => '372',
   'KISHTTP'     => '1304',
   'KISICMP'     => '724',
   'KISIMAP'     => '972',
   'KISLDAP'     => '972',
   'KISMSTATS'   => '448',
   'KISNNTP'     => '908',
   'KISNTP'      => '812',
   'KISPOP'      => '868',
   'KISRADIUS'   => '972',
   'KISRPING'    => '976',
   'KISRTSP'     => '796',
   'KISSAADHCP'  => '824',
   'KISSAADLSW'  => '928',
   'KISSAADNS'   => '876',
   'KISSAAFTP'   => '876',
   'KISSAAHTTP'  => '924',
   'KISSAAICMP'  => '1488',
   'KISSAAJITT'  => '1040',
   'KISSAASNA'   => '992',
   'KISSAAUDP'   => '976',
   'KISSAAVOIP'  => '1040',
   'KISSIP'      => '988',
   'KISSISTATS'  => '996',
   'KISSMTP'     => '1052',
   'KISSNMP'     => '1476',
   'KISSOAP'     => '788',
   'KISSSTATS'   => '372',
   'KISTCPPORT'  => '828',
   'KISTFTP'     => '956',
   'KISTRANSX'   => '1008',
   'KISTRANSX2'  => '744',
   'KISWMS'      => '924',
   'KKAAVAIL'    => '3244',
   'KKAECOACTC'  => '156',
   'KKAECOACTF'  => '419',
   'KKAECOEDCF'  => '423',
   'KKAECOEDFL'  => '1037',
   'KKAECOEDHF'  => '614',
   'KKAECOEDRF'  => '487',
   'KKAECOEDSF'  => '359',
   'KKAECOTHRU'  => '192',
   'KKAPOBJST'   => '260',
   'KLOLOGEVTS'  => '6928',
   'KLOLOGFRX'   => '814',
   'KLOLOGFST'   => '916',
   'KLOLOGPEVT'  => '6928',
   'KLOPOBJST'   => '360',
   'KLOTHPLST'   => '96',
   'KLZCPU'      => '136',
   'KLZCPUAVG'   => '132',
   'KLZDISK'     => '948',
   'KLZDSKIO'    => '192',
   'KLZDU'       => '408',
   'KLZIOEXT'    => '272',
   'KLZLOGIN'    => '488',
   'KLZLPAR'     => '344',
   'KLZNET'      => '368',
   'KLZNFS'      => '384',
   'KLZPASALRT'  => '484',
   'KLZPASCAP'   => '3064',
   'KLZPASMGMT'  => '526',
   'KLZPASSTAT'  => '1382',
   'KLZPROC'     => '1620',
   'KLZPUSR'     => '1580',
   'KLZRPC'      => '144',
   'KLZSCRPTS'   => '3952',
   'KLZSCRRTM'   => '3544',
   'KLZSCRTSM'   => '3544',
   'KLZSOCKD'    => '296',
   'KLZSOCKS'    => '100',
   'KLZSWPRT'    => '128',
   'KLZSYS'      => '288',
   'KLZTCP'      => '88',
   'KLZVM'       => '268',
   'KM5ASSTGSK'  => '164',
   'KM5CMSTGSK'  => '200',
   'KM5STGSTAT'  => '270',
   'KM6AGTSTA'   => '464',
   'KM6AGTTRAN'  => '208',
   'KM6CALL'     => '480',
   'KM6CALLLOG'  => '876',
   'KM6CALLOUT'  => '500',
   'KM6CALLRES'  => '504',
   'KM6CMDARG'   => '1200',
   'KM6EXIT'     => '260',
   'KM6FTEPOS'   => '260',
   'KM6POBJST'   => '260',
   'KM6SCHDLOG'  => '1588',
   'KM6SCHITEM'  => '880',
   'KM6SCHSUPP'  => '672',
   'KM6SUPPMNT'  => '644',
   'KM6TACTST'   => '3452',
   'KM6THPLST'   => '132',
   'KM6TRANLOG'  => '1432',
   'KM6TRANTRI'  => '508',
   'KM6TRSITEM'  => '1472',
   'KM6TRSMETA'  => '432',
   'KMCPRCA'     => '1236',
   'KN3AGS'      => '220',
   'KN3BPD'      => '154',
   'KN3BPE'      => '94',
   'KN3BPG'      => '66',
   'KN3BPS'      => '72',
   'KN3CMD'      => '674',
   'KN3CSM'      => '172',
   'KN3CSO'      => '166',
   'KN3CTA'      => '596',
   'KN3EEC'      => '248',
   'KN3EED'      => '238',
   'KN3FSE'      => '377',
   'KN3FTP'      => '2469',
   'KN3GCG'      => '98',
   'KN3GCT'      => '80',
   'KN3GIC'      => '230',
   'KN3GIG'      => '84',
   'KN3GTC'      => '276',
   'KN3GUC'      => '124',
   'KN3HPR'      => '559',
   'KN3IFA'      => '129',
   'KN3IFE'      => '343',
   'KN3IFR'      => '308',
   'KN3IFS'      => '304',
   'KN3IFW'      => '200',
   'KN3ISS'      => '360',
   'KN3RTA'      => '312',
   'KN3SCS'      => '104',
   'KN3SNA'      => '72',
   'KN3TAP'      => '686',
   'KN3TAS'      => '621',
   'KN3TCH'      => '413',
   'KN3TCL'      => '287',
   'KN3TCN'      => '667',
   'KN3TCP'      => '643',
   'KN3TCS'      => '756',
   'KN3TDV'      => '430',
   'KN3TGA'      => '600',
   'KN3THC'      => '388',
   'KN3THE'      => '478',
   'KN3THS'      => '586',
   'KN3THT'      => '482',
   'KN3TIF'      => '469',
   'KN3TLP'      => '104',
   'KN3TNA'      => '462',
   'KN3TPO'      => '761',
   'KN3TPV'      => '468',
   'KN3TSL'      => '608',
   'KN3TTC'      => '388',
   'KN3TTE'      => '422',
   'KN3TTS'      => '476',
   'KN3TTT'      => '418',
   'KN3UDP'      => '356',
   'KN3VAS'      => '244',
   'KN3VIO'      => '70',
   'KN4IFTABLE'  => '643',
   'KN4IFTOIPM'  => '719',
   'KN4INTERFA'  => '52',
   'KN4IP'       => '136',
   'KN4IPADDRT'  => '124',
   'KN4IPROUTE'  => '244',
   'KN4NMAPOS'   => '360',
   'KN4POBJST'   => '360',
   'KN4SNMP'     => '172',
   'KN4SYSTEM'   => '1264',
   'KN4TCP'      => '108',
   'KN4TCPCONN'  => '124',
   'KN4THPLST'   => '132',
   'KN4UDP'      => '68',
   'KN4UDPTABL'  => '84',
   'KNAAPP'      => '210',
   'KNADSD'      => '323',
   'KNADSH'      => '264',
   'KNADTA'      => '331',
   'KNAHEA'      => '116',
   'KNARD1'      => '208',
   'KNARD2'      => '304',
   'KNARD3'      => '108',
   'KNARD4'      => '408',
   'KNARI1'      => '384',
   'KNARI2'      => '384',
   'KNARSC'      => '612',
   'KNASEA'      => '52',
   'KNATCA'      => '52',
   'KNATCI'      => '368',
   'KNATCO'      => '601',
   'KNAWL3'      => '76',
   'KNAWL7'      => '228',
   'KNOAVAIL'    => '3244',
   'KNONCOECNA'  => '132',
   'KNONCOECNC'  => '152',
   'KNONCOECNE'  => '164',
   'KNONCOECNI'  => '352',
   'KNONCOECNG'  => '268',
   'KNONCOECNI'  => '352',
   'KNONCOECNK'  => '379',
   'KNONCOECNM'  => '184',
   'KNONCOEDCF'  => '403',
   'KNONCOEDFL'  => '136',
   'KNONCOEDNB'  => '200',
   'KNOPOBJST'   => '360',
   'KNOTHPLST'   => '132',
   'KNPAGTSTS'   => '156',
   'KNPAVAIL'    => '3244',
   'KNPCAPPACT'  => '52',
   'KNPCURDISC'  => '68',
   'KNPDEVPOLL'  => '156',
   'KNPLSTDISC'  => '188',
   'KNPMIBOBJ'   => '52',
   'KNPNETELEM'  => '84',
   'KNPNODETO'   => '56',
   'KNPOBJDISC'  => '64',
   'KNPPACPROC'  => '56',
   'KNPPOBJST'   => '260',
   'KNPPOLLPER'  => '1096',
   'KNPSNMPAC'   => '56',
   'KNPSNMPERR'  => '56',
   'KNPTOTENT'   => '52',
   'KNPWORKQUE'  => '52',
   'KNTPASALRT'  => '484',
   'KNTPASCAP'   => '3000',
   'KNTPASMGMT'  => '526',
   'KNTPASSTAT'  => '1392',
   'KNTRASPT'    => '220',
   'KNTRASTOT'   => '288',
   'KNTSCRTSM'   => '3544',
   'KNU01HOST'   => '952',
   'KNU02AGREG'  => '348',
   'KNU03VOL'    => '532',
   'KNU04LUN'    => '424',
   'KNUHOSTNIF'  => '419',
   'KNUPOBJST'   => '260',
   'KOQBTCHS'    => '328',
   'KOQCSQLR'    => '1124',
   'KOQDBD'      => '2712',
   'KOQDBMIR'    => '924',
   'KOQDBS'      => '248',
   'KOQDEVD'     => '1420',
   'KOQFGRPD'    => '980',
   'KOQJOBD'     => '1096',
   'KOQJOBS'     => '248',
   'KOQLOCK'     => '650',
   'KOQLOCKS'    => '1050',
   'KOQLOKSU'    => '276',
   'KOQLRTS'     => '216',
   'KOQLSDBD'    => '1768',
   'KOQLSERR'    => '1154',
   'KOQLSJBD'    => '1414',
   'KOQMEMGR'    => '416',
   'KOQPRCD'     => '930',
   'KOQPRCS'     => '276',
   'KOQPROBD'    => '776',
   'KOQPROBS'    => '256',
   'KOQRPOOL'    => '800',
   'KOQSCFG'     => '285',
   'KOQSRVCD'    => '592',
   'KOQSRVD'     => '660',
   'KOQSRVR'     => '256',
   'KOQSRVS'     => '432',
   'KOQSTATD'    => '264',
   'KOQSTATS'    => '284',
   'KOQTBLD'     => '1400',
   'KOQWLGS'     => '752',
   'KORADVQS'    => '2437',
   'KORALRTD'    => '708',
   'KORALRTS'    => '1046',
   'KORARCDD'    => '2624',
   'KORCACHE'    => '454',
   'KORCACHX'    => '568',
   'KORCONFS'    => '1120',
   'KORDB'       => '320',
   'KORDISPD'    => '352',
   'KORDUMPD'    => '2612',
   'KORFILES'    => '655',
   'KORFILEX'    => '577',
   'KORHSAD'     => '685',
   'KORJOBS'     => '736',
   'KORLCONF'    => '334',
   'KORLIBCU'    => '323',
   'KORLIBCX'    => '328',
   'KORLISTD'    => '352',
   'KORLKCS'     => '194',
   'KORLOCKS'    => '440',
   'KORLOGS'     => '282',
   'KORLOGSX'    => '320',
   'KORNETS'     => '224',
   'KORNETSX'    => '236',
   'KORPRCAS'    => '964',
   'KORPROCD'    => '611',
   'KORPROCS'    => '256',
   'KORRBST'     => '401',
   'KORRBSTX'    => '423',
   'KORREDOS'    => '275',
   'KORSESDX'    => '2238',
   'KORSESSD'    => '2248',
   'KORSESSS'    => '244',
   'KORSGA'      => '388',
   'KORSRVR'     => '2692',
   'KORSRVRD'    => '246',
   'KORSRVRE'    => '324',
   'KORSTASX'    => '1052',
   'KORSTATD'    => '455',
   'KORSTATE'    => '368',
   'KORSTATS'    => '484',
   'KORTBRSW'    => '283',
   'KORTRANS'    => '1916',
   'KORTS'       => '516',
   'KORTSX'      => '524',
   'KORUNDOS'    => '256',
   'KOYCACD'     => '754',
   'KOYCACS'     => '634',
   'KOYDBD'      => '484',
   'KOYDBS'      => '244',
   'KOYDEVD'     => '1006',
   'KOYENGD'     => '677',
   'KOYENGS'     => '280',
   'KOYLCKD'     => '431',
   'KOYLCKS'     => '666',
   'KOYLOCK'     => '380',
   'KOYLOCKS'    => '478',
   'KOYLOGD'     => '282',
   'KOYLOGS'     => '226',
   'KOYPRCD'     => '950',
   'KOYPRCS'     => '382',
   'KOYPROBD'    => '792',
   'KOYPROBS'    => '248',
   'KOYSCFG'     => '445',
   'KOYSDEVD'    => '898',
   'KOYSEGD'     => '584',
   'KOYSQL'      => '568',
   'KOYSQLD'     => '282',
   'KOYSRVD'     => '570',
   'KOYSRVR'     => '256',
   'KOYSRVRE'    => '732',
   'KOYSRVS'     => '292',
   'KOYSTATD'    => '262',
   'KOYSTATS'    => '260',
   'KOYTSKD'     => '282',
   'KP1CIMOMS'   => '1317',
   'KP1CIMOV'    => '407',
   'KP1COMPA'    => '847',
   'KP1COMPOV'   => '407',
   'KP1COMPUTE'  => '1024',
   'KP1DASH'     => '292',
   'KP1DATA'     => '1172',
   'KP1DATSRV'   => '352',
   'KP1DATSRVS'  => '276',
   'KP1DEVSRV'   => '312',
   'KP1DEVSRVS'  => '398',
   'KP1DISK'     => '1364',
   'KP1FABOV'    => '184',
   'KP1FABRIC'   => '225',
   'KP1FABRICA'  => '740',
   'KP1HBA'      => '1686',
   'KP1HYPER'    => '507',
   'KP1HYPOV'    => '407',
   'KP1INBAND'   => '695',
   'KP1JOB'      => '316',
   'KP1NAPI'     => '768',
   'KP1NAPIOV'   => '280',
   'KP1OTHER'    => '968',
   'KP1OUTBAND'  => '656',
   'KP1PM'       => '1067',
   'KP1PMOV'     => '1067',
   'KP1POBJST'   => '360',
   'KP1POOL'     => '2376',
   'KP1PROBE'    => '416',
   'KP1PROBEOV'  => '727',
   'KP1SCHED'    => '518',
   'KP1SDSPOS'   => '360',
   'KP1STASANB'  => '181',
   'KP1STASANC'  => '167',
   'KP1STATPCB'  => '188',
   'KP1SUBA'     => '464',
   'KP1SUBOV'    => '252',
   'KP1SUBSYST'  => '988',
   'KP1SWITCH'   => '1356',
   'KP1SWITCHA'  => '464',
   'KP1SWOV'     => '407',
   'KP1TAPE'     => '1056',
   'KP1TAPEA'    => '464',
   'KP1TAPEOV'   => '407',
   'KP1TCHPOS'   => '360',
   'KP1TFSPOS'   => '360',
   'KP1THPLST'   => '132',
   'KP1TPC'      => '552',
   'KP1TSSPOS'   => '360',
   'KP1USRS'     => '220',
   'KP1VMOV'     => '280',
   'KP1VMWARED'  => '784',
   'KP1VOLUME'   => '3152',
   'KP2LANTCP'   => '380',
   'KP2LOGDSK'   => '420',
   'KP2POBJST'   => '360',
   'KP2SYSTEM'   => '356',
   'KP2THPLST'   => '132',
   'KP8AS'       => '360',
   'KP8ASCS'     => '1339',
   'KP8ASPS'     => '1080',
   'KP8ASQS'     => '1343',
   'KP8AVAIL'    => '3244',
   'KP8CCC'      => '307',
   'KP8DCONFIG'  => '1440',
   'KP8IL'       => '307',
   'KP8ITMPSAV'  => '123',
   'KP8POBJST'   => '360',
   'KP8SDSC'     => '335',
   'KP8SL'       => '375',
   'KP8SPCA'     => '570',
   'KP8SPTA'     => '570',
   'KP8SRSC'     => '359',
   'KP8THPLST'   => '132',
   'KP9AVAIL'    => '3244',
   'KP9DSC'      => '335',
   'KP9IL'       => '123',
   'KP9ITMAGAV'  => '138',
   'KP9PCA'      => '570',
   'KP9POBJST'   => '360',
   'KP9PRLR1'    => '829',
   'KP9PRLR30'   => '829',
   'KP9PRLR7'    => '829',
   'KP9PSPS'     => '1080',
   'KP9PSQS'     => '1339',
   'KP9PTA'      => '570',
   'KP9SRSC'     => '359',
   'KP9THPLST'   => '132',
   'KPAGEND32F'  => '420',
   'KPAGEND32S'  => '604',
   'KPAGEND64F'  => '420',
   'KPAGEND64S'  => '604',
   'KPAGENI32F'  => '408',
   'KPAGENI32S'  => '604',
   'KPAGENI64F'  => '412',
   'KPAGENI64S'  => '604',
   'KPAMAGENT'   => '536',
   'KPAMDB'      => '488',
   'KPAMSAGENT'  => '360',
   'KPAMTASK'    => '584',
   'KPH02VERSI'  => '534',
   'KPH03CPUSU'  => '92',
   'KPH04PAGIN'  => '72',
   'KPH05PHYSI'  => '72',
   'KPH06FILES'  => '552',
   'KPH07PROCE'  => '832',
   'KPH08MANAG'  => '412',
   'KPH09MANAC'  => '576',
   'KPH10MANAL'  => '716',
   'KPH11CLPEV'  => '560',
   'KPHPOBJST'   => '260',
   'KPHSRVRDAG'  => '169',
   'KPHSVRCPUP'  => '540',
   'KPHSVRDETS'  => '544',
   'KPHSVRLPAR'  => '892',
   'KPHSVRPOS'   => '260',
   'KPK02GLOBA'  => '440',
   'KPK03PERLP'  => '940',
   'KPK03TADDM'  => '148',
   'KPK05CPUPL'  => '240',
   'KPK05MONLP'  => '788',
   'KPK07MUALC'  => '316',
   'KPK08MPOOL'  => '192',
   'KPK09AMELP'  => '616',
   'KPK10FAIL'   => '202',
   'KPKDIRE'     => '118',
   'KPK03PERLP'  => '892',
   'KPKPOBJST'   => '260',
   'KPPCDCSES1'  => '137',
   'KPPCHNL1'    => '77',
   'KPPCOMMON1'  => '1288',
   'KPPDASD1'    => '264',
   'KPPDASDDV1'  => '70',
   'KPPDASDP1'   => '156',
   'KPPDASDPS1'  => '108',
   'KPPDASDST1'  => '112',
   'KPPENHCHL1'  => '171',
   'KPPIS1'      => '400',
   'KPPLODIC1'   => '68',
   'KPPLODICU1'  => '68',
   'KPPLPARTI1'  => '208',
   'KPPMPIF1'    => '117',
   'KPPMQQC'     => '361',
   'KPPMQQD'     => '485',
   'KPPMQSSUM1'  => '436',
   'KPPMQSUM1'   => '88',
   'KPPPDUSER1'  => '128',
   'KPPPOBJST'   => '360',
   'KPPPROCT1'   => '112',
   'KPPSSM_TI1'  => '340',
   'KPPSSU_TI1'  => '360',
   'KPPSSUTIL1'  => '63',
   'KPPSYSBLK1'  => '160',
   'KPPSYSLST1'  => '88',
   'KPPSYSMSG1'  => '168',
   'KPPSYSSHT1'  => '184',
   'KPPSYSTRC1'  => '87',
   'KPPTAPE1'    => '172',
   'KPPTCPIP1'   => '356',
   'KPPTHPLST'   => '132',
   'KPPTSLICE1'  => '120',
   'KPPVFADE1'   => '340',
   'KPPVFADS1'   => '120',
   'KPX02TOP50'  => '2460',
   'KPX03TOP50'  => '2472',
   'KPX08CPUSU'  => '420',
   'KPX09CPUDE'  => '232',
   'KPX11SYSTE'  => '80',
   'KPX12SYSTE'  => '68',
   'KPX13PAGIN'  => '76',
   'KPX14LOGIC'  => '1076',
   'KPX15WORKL'  => '904',
   'KPX16NIMRE'  => '2256',
   'KPX17PRINT'  => '1392',
   'KPX19PHYSI'  => '84',
   'KPX20VIRTU'  => '100',
   'KPX23PROCE'  => '80',
   'KPX24PROCE'  => '2732',
   'KPX26DISKS'  => '564',
   'KPX27PHYSI'  => '396',
   'KPX28VOLUM'  => '276',
   'KPX29LOGIC'  => '1204',
   'KPX30FILES'  => '1028',
   'KPX32NETWO'  => '1527',
   'KPX33NETWO'  => '4008',
   'KPX34NETWO'  => '1008',
   'KPX35INTER'  => '76',
   'KPX36INTER'  => '180',
   'KPX37TCP'    => '88',
   'KPX41DEFIN'  => '1636',
   'KPX42ACTIV'  => '1680',
   'KPX46WPARC'  => '336',
   'KPX47WPPHM'  => '336',
   'KPX48WPNET'  => '1328',
   'KPX48WPNET'  => '1328',
   'KPX49WPFIL'  => '1584',
   'KPX50WPINF'  => '5448',
   'KPX50WPINF'  => '5448',
   'KPX51DEVIC'  => '528',
   'KPX51MPIOS'  => '528',
   'KPX52MPIOA'  => '528',
   'KPX53MPOOL'  => '144',
   'KPX54QOS'    => '808',
   'KPX55AME'    => '452',
   'KPX56TADDM'  => '152',
   'KPXPOBJST'   => '260',
   'KQ5AVAIL'    => '3244',
   'KQ5B10RG'    => '280',
   'KQ5B05PHYS'  => '256',
   'KQ5B10RG'    => '280',
   'KQ5B15RLL'   => '68',
   'KQ5B20LOGI'  => '624',
   'KQ5B25LOGI'  => '456',
   'KQ5B25RTDR'  => '456',
   'KQ5B30LOGI'  => '456',
   'KQ5B30RLL'   => '68',
   'KQ5B35LOGI'  => '456',
   'KQ5C20RES'   => '696',
   'KQ5C30RLL'   => '68',
   'KQ5CLUCSVP'  => '184',
   'KQ5CLUSCSV'  => '384',
   'KQ5CLUSTE0'  => '672',
   'KQ5CLUSRSC'  => '160',
   'KQ5CLUSTE1'  => '164',
   'KQ5CLUSTE3'  => '160',
   'KQ5CLUSTER'  => '172',
   'KQ5CLUSUM'   => '444',
   'KQ5CSVSUMM'  => '256',
   'KQ5D20NODE'  => '756',
   'KQ5D30RLL'   => '68',
   'KQ5D40CPU'   => '188',
   'KQ5D50RLL'   => '68',
   'KQ5D55RLL'   => '68',
   'KQ5D60MEM'   => '228',
   'KQ5D70RLL'   => '68',
   'KQ5D75RLL'   => '68',
   'KQ5D80HDD'   => '300',
   'KQ5D85RLL'   => '68',
   'KQ5D90RLL'   => '68',
   'KQ5E20NET'   => '460',
   'KQ5E30RLL'   => '68',
   'KQ5EVTLOG'   => '2418',
   'KQ5F20INT'   => '756',
   'KQ5F30RLL'   => '68',
   'KQ5F40NET'   => '328',
   'KQ5F50RLL'   => '68',
   'KQ5F60RLL'   => '68',
   'KQ5F70RLL'   => '68',
   'KQ5G20RISK'  => '488',
   'KQ5G30RLL'   => '268',
   'KQ5MSCLUST'  => '252',
   'KQ5NETMESS'  => '144',
   'KQ5NWRECON'  => '164',
   'KQ5POBJST'   => '360',
   'KQ5THPLST'   => '132',
   'KQ5WIN32CO'  => '112',
   'KQ7ACTIVES'  => '164',
   'KQ7APPLWAS'  => '312',
   'KQ7APPPOOL'  => '256',
   'KQ7ASPNET4'  => '424',
   'KQ7ASPNETA'  => '204',
   'KQ7ASPNETF'  => '204',
   'KQ7AVAIL'    => '3244',
   'KQ7EVTLOG'   => '2418',
   'KQ7FSITDTL'  => '564',
   'KQ7FTPBIND'  => '240',
   'KQ7FTPSERV'  => '392',
   'KQ7HTTPCUS'  => '368',
   'KQ7HTTPERR'  => '1514',
   'KQ7IISAPPL'  => '588',
   'KQ7IISCOMP'  => '116',
   'KQ7IISFTPI'  => '120',
   'KQ7IISFTPM'  => '308',
   'KQ7IISFTPS'  => '116',
   'KQ7IISNNT0'  => '120',
   'KQ7IISNNT2'  => '308',
   'KQ7IISNNTP'  => '116',
   'KQ7IISSMM'   => '308',
   'KQ7IISSMT0'  => '120',
   'KQ7IISSMTP'  => '116',
   'KQ7IISWEB1'  => '308',
   'KQ7IISWEBI'  => '120',
   'KQ7IISWEBS'  => '116',
   'KQ7INTERNE'  => '164',
   'KQ7MIMETYP'  => '176',
   'KQ7POBJST'   => '360',
   'KQ7RESTRIC'  => '248',
   'KQ7SITECER'  => '628',
   'KQ7THPLST'   => '132',
   'KQ7WEBBIND'  => '304',
   'KQ7WEBSER1'  => '164',
   'KQ7WEBSERV'  => '364',
   'KQ7WIN32P0'  => '164',
   'KQ7WIN32P1'  => '224',
   'KQ7WIN32PE'  => '280',
   'KQ7WSITDTL'  => '628',
   'KQAAVAIL'    => '3244',
   'KQAEVTLOG'   => '2212',
   'KQAPOBJST'   => '360',
   'KQAT0ALERT'  => '1016',
   'KQAXARRAY'   => '1012',
   'KQAXCACHEI'  => '48',
   'KQAXCACHET'  => '48',
   'KQAXCACHEZ'  => '272',
   'KQAXCACON'   => '160',
   'KQAXCOMPRI'  => '48',
   'KQAXCOMPRT'  => '48',
   'KQAXCOMPRZ'  => '152',
   'KQAXDIFFSI'  => '48',
   'KQAXDIFFST'  => '48',
   'KQAXDIFFSZ'  => '432',
   'KQAXEMAILT'  => '72',
   'KQAXFWENGI'  => '48',
   'KQAXFWENGT'  => '48',
   'KQAXFWENGZ'  => '192',
   'KQAXFWSRVI'  => '48',
   'KQAXFWSRVT'  => '48',
   'KQAXFWSRVZ'  => '228',
   'KQAXGLOBAL'  => '2332',
   'KQAXH323FI'  => '48',
   'KQAXH323FT'  => '48',
   'KQAXH323FZ'  => '64',
   'KQAXHTTPST'  => '232',
   'KQAXLOWLS'   => '96',
   'KQAXMALWRT'  => '512',
   'KQAXNETWK'   => '488',
   'KQAXPROXYI'  => '48',
   'KQAXPROXYT'  => '48',
   'KQAXPROXYZ'  => '688',
   'KQAXSERVER'  => '880',
   'KQAXSOCKSI'  => '48',
   'KQAXSOCKST'  => '48',
   'KQAXSOCKSZ'  => '128',
   'KQAXSTORE'   => '668',
   'KQAXURLFLT'  => '296',
   'KQBAVAIL'    => '3244',
   'KQBBAMINTC'  => '180',
   'KQBBIZAPP'   => '882',
   'KQBBIZTDDS'  => '268',
   'KQBDELCHN'   => '864',
   'KQBDISTRIB'  => '872',
   'KQBEVENPD'   => '884',
   'KQBEVENTS'   => '864',
   'KQBEVTLOG'   => '2212',
   'KQBFILERCV'  => '284',
   'KQBFILESND'  => '232',
   'KQBFTPRECV'  => '232',
   'KQBFTPSEND'  => '232',
   'KQBGENERA'   => '916',
   'KQBHOSTTHR'  => '1054',
   'KQBHSTGRP'   => '2602',
   'KQBHTTPRCV'  => '224',
   'KQBHTTPSND'  => '192',
   'KQBHUMANWO'  => '68',
   'KQBMESSAG1'  => '308',
   'KQBMESSLAT'  => '212',
   'KQBMSBTRLS'  => '3982',
   'KQBMSBTSG0'  => '663',
   'KQBMSBTSG1'  => '663',
   'KQBMSBTSG2'  => '663',
   'KQBMSBTSG3'  => '663',
   'KQBMSBTSIS'  => '4202',
   'KQBMSBTSMS'  => '588',
   'KQBMSBTSOS'  => '1062',
   'KQBMSBTSPS'  => '2508',
   'KQBMSGBOXG'  => '188',
   'KQBMSGBOXH'  => '164',
   'KQBMSMQRCV'  => '232',
   'KQBMSMQSND'  => '232',
   'KQBNOTIFI'   => '920',
   'KQBORADB'    => '156',
   'KQBORAEBIZ'  => '156',
   'KQBORCHEST'  => '444',
   'KQBPOBJST'   => '360',
   'KQBPOP3RCV'  => '216',
   'KQBSAPAD'    => '156',
   'KQBSIEBELA'  => '156',
   'KQBSMTPSND'  => '168',
   'KQBSOAPRCV'  => '168',
   'KQBSOAPSND'  => '168',
   'KQBSQLAD'    => '156',
   'KQBSQLRECV'  => '168',
   'KQBSQLSEND'  => '168',
   'KQBSSODB'    => '1038',
   'KQBSUBSCR'   => '872',
   'KQBSUBSCRP'  => '868',
   'KQBVACUUM'   => '880',
   'KQBWSADPTR'  => '236',
   'KQBWSSADAP'  => '136',
   'KQFASPNAP2'  => '184',
   'KQFASPNAP4'  => '520',
   'KQFASPNE64'  => '188',
   'KQFASPNEF2'  => '184',
   'KQFASPNET'   => '128',
   'KQFASPNET0'  => '468',
   'KQFASPNET2'  => '160',
   'KQFASPNET4'  => '128',
   'KQFASPNET6'  => '392',
   'KQFASPNETA'  => '584',
   'KQFASPNETF'  => '520',
   'KQFASPNETV'  => '104',
   'KQFASPNFI'   => '128',
   'KQFDATAPRO'  => '224',
   'KQFEVTLOG'   => '2418',
   'KQFNETCLR0'  => '200',
   'KQFNETCLR4'  => '420',
   'KQFNETCLRE'  => '156',
   'KQFNETCLRF'  => '420',
   'KQFNETCLRI'  => '124',
   'KQFNETCLRJ'  => '156',
   'KQFNETCLRL'  => '240',
   'KQFNETCLRM'  => '260',
   'KQFNETCLRN'  => '420',
   'KQFNETCLRR'  => '164',
   'KQFNETCLRS'  => '144',
   'KQFNETPROC'  => '460',
   'KQFNETVER'   => '198',
   'KQFORACLDP'  => '224',
   'KQFPOBJST'   => '260',
   'KQFSERMODE'  => '636',
   'KQFSERMSER'  => '740',
   'KQFSERVICE'  => '636',
   'KQFSMOPER4'  => '692',
   'KQFSMOPERA'  => '692',
   'KQFSMSERV4'  => '740',
   'KQFSMSVCH4'  => '220',
   'KQFSMSVCHO'  => '220',
   'KQFWIN32P4'  => '308',
   'KQFWIN32P5'  => '308',
   'KQFWIN32PE'  => '224',
   'KQFWIN32S0'  => '636',
   'KQFWIN32S1'  => '692',
   'KQFWIN32S2'  => '740',
   'KQFWIN32S3'  => '220',
   'KQFWORKFL4'  => '308',
   'KQHAPPINT1'  => '500',
   'KQHAPPINTE'  => '444',
   'KQHAVAIL'    => '3244',
   'KQHEVTLOG'   => '2212',
   'KQHHISDATA'  => '240',
   'KQHMANAGE0'  => '224',
   'KQHMQBRID1'  => '72',
   'KQHMQBRID2'  => '208',
   'KQHMQBRID3'  => '208',
   'KQHMQBRID4'  => '208',
   'KQHMQBRID5'  => '208',
   'KQHMSFTDB2'  => '508',
   'KQHMSHIS01'  => '124',
   'KQHMSHISM1'  => '136',
   'KQHMSHISM2'  => '244',
   'KQHMSHISM3'  => '148',
   'KQHMSHISMQ'  => '436',
   'KQHMSHIST1'  => '64',
   'KQHMSHIST2'  => '80',
   'KQHMSHIST3'  => '56',
   'KQHMSHIST4'  => '72',
   'KQHMSHIST5'  => '72',
   'KQHMSHIST6'  => '80',
   'KQHMSHIST7'  => '80',
   'KQHMSHIST8'  => '80',
   'KQHMSHIST9'  => '84',
   'KQHMSHISTR'  => '56',
   'KQHMSSNA10'  => '196',
   'KQHMSSNA11'  => '180',
   'KQHMSSNA12'  => '192',
   'KQHMSSNA13'  => '283',
   'KQHMSSNA14'  => '1072',
   'KQHMSSNA15'  => '223',
   'KQHMSSNAA0'  => '199',
   'KQHMSSNAC0'  => '1451',
   'KQHMSSNAD0'  => '1172',
   'KQHMSSNAL0'  => '207',
   'KQHMSSNAL1'  => '4903',
   'KQHMSSNAL2'  => '211',
   'KQHMSSNAL3'  => '239',
   'KQHMSSNAL4'  => '231',
   'KQHMSSNALI'  => '1101',
   'KQHMSSNAP0'  => '159',
   'KQHMSSNAPO'  => '147',
   'KQHMSSNAPR'  => '4368',
   'KQHMSSNAS0'  => '284',
   'KQHMSSNAS1'  => '976',
   'KQHMSSNAS2'  => '368',
   'KQHMSSNAS3'  => '188',
   'KQHMSSNAS4'  => '228',
   'KQHMSSNAS5'  => '224',
   'KQHMSSNAS6'  => '180',
   'KQHMSSNAS7'  => '880',
   'KQHMSSNAS8'  => '1792',
   'KQHMSSNAS9'  => '180',
   'KQHMSSNAST'  => '184',
   'KQHPOBJST'   => '360',
   'KQHSESSIO1'  => '140',
   'KQHSESSIO2'  => '236',
   'KQHSNA3270'  => '168',
   'KQHSNACON0'  => '212',
   'KQHSNALOG0'  => '212',
   'KQHTN3270S'  => '268',
   'KQITACMF'    => '1792',
   'KQITACND'    => '2008',
   'KQITACTH'    => '1652',
   'KQITACTR'    => '2072',
   'KQITASMF'    => '1640',
   'KQITASND'    => '1736',
   'KQITASTH'    => '1380',
   'KQITASTR'    => '1704',
   'KQITBREV'    => '1712',
   'KQITBRKR'    => '1620',
   'KQITBRKS'    => '1156',
   'KQITBSEV'    => '944',
   'KQITCOMP'    => '852',
   'KQITDFEG'    => '1272',
   'KQITDFFN'    => '4016',
   'KQITDFMF'    => '1944',
   'KQITDSEA'    => '1816',
   'KQITDSEN'    => '808',
   'KQITDSER'    => '2176',
   'KQITDSES'    => '3356',
   'KQITEGRS'    => '744',
   'KQITFLEV'    => '2856',
   'KQITMFLS'    => '1692',
   'KQITMNBR'    => '892',
   'KQITMNEG'    => '1144',
   'KQITMNEV'    => '1576',
   'KQITMNFN'    => '1732',
   'KQITMNMF'    => '1300',
   'KQITMNSF'    => '1548',
   'KQITPREV'    => '1176',
   'KQITPSMG'    => '1048',
   'KQITPSMS'    => '728',
   'KQITPSMT'    => '1496',
   'KQITPSST'    => '1044',
   'KQITRSFL'    => '1024',
   'KQITRSJD'    => '1272',
   'KQITRSJV'    => '1008',
   'KQITRSOD'    => '1012',
   'KQITRSPS'    => '1064',
   'KQITRSSP'    => '1152',
   'KQITSTBR'    => '1148',
   'KQITSTEG'    => '1656',
   'KQITSTFN'    => '3012',
   'KQITSTMF'    => '2068',
   'KQITSTSF'    => '2572',
   'KQPASPNET'   => '432',
   'KQPAVAIL'    => '3244',
   'KQPDOCUMEN'  => '68',
   'KQPEVTLOG'   => '2418',
   'KQPEXCELCA'  => '200',
   'KQPEXCELSE'  => '84',
   'KQPEXCELWE'  => '96',
   'KQPINFOPAT'  => '340',
   'KQPOFFICE4'  => '188',
   'KQPOFFICE5'  => '272',
   'KQPOFFICE6'  => '536',
   'KQPOFFICE7'  => '416',
   'KQPOFFICE8'  => '192',
   'KQPPOBJST'   => '260',
   'KQPSEARC0'   => '156',
   'KQPSEARCH0'  => '536',
   'KQPSEARCHA'  => '188',
   'KQPSEARCHC'  => '260',
   'KQPSEARCHG'  => '272',
   'KQPSEARCHI'  => '196',
   'KQPSEARCHS'  => '192',
   'KQPSEARCHT'  => '180',
   'KQPSERVSUM'  => '1248',
   'KQPSHARE10'  => '188',
   'KQPSHARE11'  => '536',
   'KQPSHARE12'  => '416',
   'KQPSHARE13'  => '192',
   'KQPSHAREDS'  => '292',
   'KQPSHAREP0'  => '200',
   'KQPSHAREP1'  => '228',
   'KQPSHAREP2'  => '352',
   'KQPSHAREP3'  => '392',
   'KQPSHAREP8'  => '548',
   'KQPSHAREP9'  => '272',
   'KQPSPPVER'   => '248',
   'KQPSPROLES'  => '348',
   'KQPSSPSUMM'  => '1672',
   'KQPWEBAPPL'  => '1772',
   'KQPWEBSERV'  => '432',
   'KQRAVAIL'    => '3244',
   'KQREVTLOG'   => '2212',
   'KQRPOBJST'   => '260',
   'KQRVMMS'     => '1172',
   'KQRVNWKS'    => '772',
   'KQXAVAIL'    => '3244',
   'KQXCITRIXL'  => '288',
   'KQXEVTLOG'   => '2212',
   'KQXICA'      => '336',
   'KQXIMA'      => '160',
   'KQXLICENSE'  => '68',
   'KQXPOBJST'   => '260',
   'KQXPRESSRV'  => '432',
   'KQXPRESSV3'  => '176',
   'KQXPRESSV4'  => '76',
   'KQXPRESV45'  => '388',
   'KQXSECURE'   => '84',
   'KR2DISK'     => '232',
   'KR2ELOGWMI'  => '2418',
   'KR2HRMEM'    => '232',
   'KR2HRSYSTE'  => '1213',
   'KR2MEMORY'   => '116',
   'KR2MEPS'     => '169',
   'KR2NICNAV'   => '427',
   'KR2PAGINGF'  => '160',
   'KR2POBJST'   => '360',
   'KR2PROCESS'  => '172',
   'KR2PROCLST'  => '260',
   'KR2PROCSR'   => '264',
   'KR2PROCSRT'  => '64',
   'KR2STORTBL'  => '204',
   'KR2SYSTEM'   => '116',
   'KR2TERMIN0'  => '160',
   'KR2TERMIN1'  => '188',
   'KR2TERMINA'  => '68',
   'KR2THPLST'   => '132',
   'KR2WDS'      => '169',
   'KR2WIN32CO'  => '700',
   'KR2WIN32OP'  => '420',
   'KR2WIN32P0'  => '212',
   'KR2WIN32PA'  => '324',
   'KR2WIN32PE'  => '204',
   'KR2WIN32PH'  => '740',
   'KR2WIN32PR'  => '256',
   'KR2WIN32S0'  => '1868',
   'KR2WIN32US'  => '396',
   'KR2WINPOS'   => '360',
   'KR2WMINNIC'  => '240',
   'KR2WMINPLS'  => '264',
   'KR2WMIPOS'   => '360',
   'KR3AIXLOGI'  => '308',
   'KR3AIXLV'    => '256',
   'KR3AIXPAGE'  => '264',
   'KR3AIXPOS'   => '360',
   'KR3AIXPV'    => '232',
   'KR3AIXUSRT'  => '396',
   'KR3AIXVG'    => '240',
   'KR3FILESYS'  => '276',
   'KR3MEMORY'   => '256',
   'KR3MEPS'     => '169',
   'KR3NIFTABL'  => '427',
   'KR3POBJST'   => '360',
   'KR3PROCLST'  => '268',
   'KR3PROCSR'   => '264',
   'KR3PROCSRT'  => '64',
   'KR3STORTBL'  => '204',
   'KR3SYSTEM'   => '1227',
   'KR3THPLST'   => '132',
   'KR3VIRTUAL'  => '92',
   'KR4DISK'     => '232',
   'KR4LNXPOS'   => '360',
   'KR4MEMORY'   => '244',
   'KR4MEPS'     => '169',
   'KR4NIFTABL'  => '427',
   'KR4POBJST'   => '360',
   'KR4PROC'     => '324',
   'KR4PROCSR'   => '76',
   'KR4STORTBL'  => '204',
   'KR4SYSTEM'   => '1215',
   'KR4THPLST'   => '132',
   'KR4VIRTUAL'  => '92',
   'KR5FILESYS'  => '248',
   'KR5HPPOS'    => '360',
   'KR5IFTABLE'  => '427',
   'KR5MEMORY'   => '252',
   'KR5MEPS'     => '169',
   'KR5POBJST'   => '360',
   'KR5PROCLST'  => '132',
   'KR5PROCSR'   => '100',
   'KR5SYSTEM'   => '1163',
   'KR5THPLST'   => '132',
   'KR6CIMDISK'  => '412',
   'KR6CIMMEM'   => '180',
   'KR6CIMNIC'   => '200',
   'KR6CIMPLST'  => '1160',
   'KR6CIMPOS'   => '360',
   'KR6CIMPROC'  => '120',
   'KR6CIMSYS'   => '168',
   'KR6DISK'     => '256',
   'KR6HRMEM'    => '216',
   'KR6HRSYSTE'  => '1212',
   'KR6IFTABLE'  => '427',
   'KR6MSNMPS'   => '169',
   'KR6MSSMA'    => '169',
   'KR6MWBEMS'   => '169',
   'KR6POBJST'   => '360',
   'KR6PROCLST'  => '272',
   'KR6PROCSR'   => '100',
   'KR6SMAPOS'   => '360',
   'KR6SMC0CPT'  => '128',
   'KR6SMC0DSK'  => '304',
   'KR6SMC0MEM'  => '188',
   'KR6SMC0NIC'  => '427',
   'KR6SMC0OS'   => '1132',
   'KR6SMC0PRO'  => '572',
   'KR6SMC0PRX'  => '340',
   'KR6SMCNFS'   => '260',
   'KR6SMCPOS'   => '360',
   'KR6SMCVXFS'  => '280',
   'KR6STORTBL'  => '204',
   'KR6THPLST'   => '132',
   'KR9AVAIL'    => '3284',
   'KR9KR9KPI'   => '483',
   'KR9KR9SCHG'  => '2074',
   'KR9KR9STAT'  => '1273',
   'KR9KR9URLC'  => '454',
   'KR9POBJST'   => '289',
   'KR9RADLOG'   => '351',
   'KR9XMLLOG'   => '596',
   'KRAHIST'     => '332',
   'KREPOBJST'   => '360',
   'KRETACTST'   => '3452',
   'KRETHPLST'   => '132',
   'KREWTCFCL1'  => '1525',
   'KREWTCFCL2'  => '1597',
   'KREWTCFCL3'  => '1569',
   'KREWTCFCLI'  => '1609',
   'KRGAGTERRM'  => '202',
   'KRGBCDEG1'   => '162',
   'KRGBCDEG2'   => '182',
   'KRGBCDEG3'   => '166',
   'KRGBCDEG4'   => '210',
   'KRGBCDEG5'   => '65',
   'KRGBCDEG6'   => '83',
   'KRGBCDEG7'   => '169',
   'KRGBCDEG8'   => '71',
   'KRGBCDSUM'   => '125',
   'KRGMCDEG1'   => '205',
   'KRGMCDEG2'   => '191',
   'KRGMCDEG3'   => '65',
   'KRGMCDEG4'   => '154',
   'KRGMCDEG5'   => '83',
   'KRGMCDEG6'   => '169',
   'KRGMCDEG7'   => '205',
   'KRGMCDSUM'   => '125',
   'KRGOCDEG1'   => '132',
   'KRGOCDEG2'   => '132',
   'KRGOCDEG3'   => '76',
   'KRGOCDEG4'   => '76',
   'KRGOCDEG5'   => '76',
   'KRGOCDSUM'   => '125',
   'KRGPOBJST'   => '260',
   'KRGTAPSUM'   => '125',
   'KRGTPDEG1'   => '65',
   'KRGTPDEG2'   => '124',
   'KRGZHEVENT'  => '210',
   'KRGZLEVENT'  => '217',
   'KRHACTLOGS'  => '126',
   'KRHAREVENT'  => '266',
   'KRHARMSGS'   => '164',
   'KRHBCDSDET'  => '200',
   'KRHBCDSSUM'  => '70',
   'KRHBKUPDSN'  => '212',
   'KRHBKUPVER'  => '192',
   'KRHBKUPVOL'  => '216',
   'KRHCDSBCKP'  => '230',
   'KRHCDSENQS'  => '228',
   'KRHCDSSPCE'  => '515',
   'KRHCDSSUM'   => '78',
   'KRHCOLEXTR'  => '287',
   'KRHCOLFNCS'  => '297',
   'KRHCOLSUMM'  => '120',
   'KRHCOLTHRS'  => '134',
   'KRHDAILYST'  => '212',
   'KRHDSMDET'   => '134',
   'KRHDSMSUM'   => '106',
   'KRHDSRFUNC'  => '156',
   'KRHDUMPCLS'  => '132',
   'KRHDUMPDSN'  => '184',
   'KRHDUMPVER'  => '472',
   'KRHDUMPVOL'  => '176',
   'KRHFILTER'   => '408',
   'KRHHLTBKUP'  => '133',
   'KRHHLTDET'   => '270',
   'KRHHLTDUMP'  => '133',
   'KRHHLTHVST'  => '133',
   'KRHHLTMIG'   => '133',
   'KRHHSMCDSS'  => '140',
   'KRHHSMCMDS'  => '328',
   'KRHHSMEXIT'  => '279',
   'KRHHSMFUNC'  => '117',
   'KRHHSMHOST'  => '384',
   'KRHHSMLOGS'  => '140',
   'KRHHSMMWES'  => '318',
   'KRHHSMPTCH'  => '232',
   'KRHHSMSSYS'  => '178',
   'KRHHSMVOLS'  => '238',
   'KRHLMIGDET'  => '148',
   'KRHLRECDET'  => '180',
   'KRHMCDDET'   => '195',
   'KRHMGRTDSN'  => '483',
   'KRHMGRTVOL'  => '290',
   'KRHMMVSUM'   => '62',
   'KRHPOBJST'   => '260',
   'KRHRCSUM'    => '132',
   'KRHSMSSMRY'  => '156',
   'KRHTAPECPY'  => '100',
   'KRHTAPEVOL'  => '135',
   'KRHVOLEST'   => '175',
   'KRHVSRFUNC'  => '151',
   'KRHXTRSUM'   => '122',
   'KRJACTREC'   => '390',
   'KRJAOSUBQU'  => '260',
   'KRJPOBJST'   => '260',
   'KRJZZAOPAL'  => '112',
   'KRNALSPC'    => '114',
   'KRNCATDSA'   => '166',
   'KRNCATSUM'   => '134',
   'KRNCATVOL'   => '122',
   'KRNCCHPRF'   => '134',
   'KRNLBKP'     => '222',
   'KRNPOBJST'   => '260',
   'KRNQACMEVT'  => '218',
   'KRVACDIAPP'  => '123',
   'KRVAGGMGMT'  => '100',
   'KRVBKUPALL'  => '142',
   'KRVCBTIBKU'  => '80',
   'KRVCBTIJOB'  => '90',
   'KRVCDSNLST'  => '150',
   'KRVDB2INV'   => '63',
   'KRVFILTER'   => '408',
   'KRVHISABMC'  => '102',
   'KRVHISABME'  => '102',
   'KRVHISCBTI'  => '102',
   'KRVICDET'    => '156',
   'KRVICREC'    => '115',
   'KRVPOBJST'   => '260',
   'KRVVOLDMPA'  => '119',
   'KRVZABRPAL'  => '138',
   'KRZACTINS'   => '784',
   'KRZACTINSR'  => '216',
   'KRZAGINF'    => '828',
   'KRZAGTLSNR'  => '1170',
   'KRZAGTNETS'  => '1928',
   'KRZARCDEST'  => '716',
   'KRZARCHIVE'  => '164',
   'KRZASMBGPS'  => '60',
   'KRZASMCLIT'  => '268',
   'KRZASMDGIO'  => '344',
   'KRZASMDISK'  => '724',
   'KRZASMDKGP'  => '420',
   'KRZASMDKIO'  => '384',
   'KRZASMFILE'  => '396',
   'KRZASMINST'  => '284',
   'KRZASMLOGS'  => '422',
   'KRZASMOPRA'  => '164',
   'KRZASMPARA'  => '1772',
   'KRZASMPOS'   => '260',
   'KRZASMPROS'  => '1176',
   'KRZASMTMPL'  => '124',
   'KRZBUFCADE'  => '220',
   'KRZBUFCART'  => '180',
   'KRZCAFURA'   => '104',
   'KRZDAFCOUT'  => '96',
   'KRZDAFIO'    => '832',
   'KRZDAFOVEW'  => '804',
   'KRZDBCABK'   => '232',
   'KRZDBCLSZ'   => '356',
   'KRZDBCLUS'   => '512',
   'KRZDBIDXS'   => '1844',
   'KRZDBINF'    => '178',
   'KRZDBINFO'   => '804',
   'KRZDBIXAB'   => '232',
   'KRZDBIXSZ'   => '356',
   'KRZDBSQLT'   => '616',
   'KRZDBTABLS'  => '748',
   'KRZDBTBNR'   => '224',
   'KRZDBTBSZ'   => '356',
   'KRZDGALOGS'  => '422',
   'KRZDGARCHD'  => '1900',
   'KRZDGARCHG'  => '72',
   'KRZDGARCHL'  => '816',
   'KRZDGARCHS'  => '1024',
   'KRZDGBGPS'   => '60',
   'KRZGCSBLO'   => '188',
   'KRZDGCUSQ'   => '1888',
   'KRZDGCUSS'   => '1304',
   'KRZDGDATAF'  => '1340',
   'KRZDGDBINF'  => '724',
   'KRZDGDKSP'   => '692',
   'KRZDGDSTST'  => '2092',
   'KRZDGLARCH'  => '816',
   'KRZDGLOG'    => '140',
   'KRZDGLOGF'   => '332',
   'KRZDGLOGHI'  => '136',
   'KRZDGLOGHS'  => '256',
   'KRZDGLOGSS'  => '176',
   'KRZDGLOGST'  => '192',
   'KRZDGMGSTD'  => '272',
   'KRZDGMGSTS'  => '168',
   'KRZDGPARA'   => '876',
   'KRZDGPOS'    => '260',
   'KRZDGRECPR'  => '180',
   'KRZDGSTATS'  => '244',
   'KRZDGSTATU'  => '480',
   'KRZDGSTDLG'  => '208',
   'KRZDGSTDPG'  => '160',
   'KRZDGSTDPO'  => '388',
   'KRZDGSTDPS'  => '100',
   'KRZDGSTDST'  => '228',
   'KRZDICCADE'  => '136',
   'KRZDICCART'  => '172',
   'KRZGCSBLO'   => '120',
   'KRZGCSCRB'   => '200',
   'KRZGCSCRL'   => '200',
   'KRZGCSMEM'   => '180',
   'KRZGESENQS'  => '148',
   'KRZGESLAT'   => '112',
   'KRZGESLOCK'  => '404',
   'KRZGESMEM'   => '260',
   'KRZINSTINF'  => '312',
   'KRZINTCON'   => '276',
   'KRZLIBCADE'  => '136',
   'KRZLIBCART'  => '188',
   'KRZMSGSTAT'  => '304',
   'KRZPOBJST'   => '260',
   'KRZRAMCLIT'  => '268',
   'KRZRAMDGIO'  => '344',
   'KRZRAMDISK'  => '808',
   'KRZRAMDKGP'  => '420',
   'KRZRAMDKIO'  => '384',
   'KRZRAMTMPL'  => '124',
   'KRZRDBBGPS'  => '156',
   'KRZRDBCUSQ'  => '1888',
   'KRZRDBCUSS'  => '1304',
   'KRZRDBDKSP'  => '721',
   'KRZRDBFDL'   => '112',
   'KRZRDBFDLF'  => '625',
   'KRZRDBFRA'   => '96',
   'KRZRDBLAT'   => '288',
   'KRZRDBLKD'   => '212',
   'KRZRDBLOGS'  => '500',
   'KRZRDBLS'    => '532',
   'KRZRDBLSES'  => '400',
   'KRZRDBOBJS'  => '480',
   'KRZRDBOPTS'  => '184',
   'KRZRDBPARA'  => '876',
   'KRZRDBPOS'   => '260',
   'KRZRDBPROD'  => '932',
   'KRZRDBPROS'  => '176',
   'KRZRDBPTA'   => '220',
   'KRZRDBRFD'   => '132',
   'KRZRDBRSD'   => '248',
   'KRZRDBRSS'   => '192',
   'KRZRDBSTAT'  => '456',
   'KRZRDBTOPO'  => '400',
   'KRZRDBCUSQ' => '1940',
   'KRZRDBUTS'   => '240',
   'KRZRDPGADT'  => '140',
   'KRZRDPGAOV'  => '548',
   'KRZRESLIMN'  => '200',
   'KRZSEGSTAT'  => '304',
   'KRZSESSDTL'  => '1732',
   'KRZSESSSMY'  => '260',
   'KRZSEWARAC'  => '224',
   'KRZSGADETL'  => '136',
   'KRZSGAOVEW'  => '372',
   'KRZSGASIZE'  => '616',
   'KRZSMETGP'   => '428',
   'KRZSMETRIC'  => '256',
   'KRZSYSSTAT'  => '160',
   'KRZTACTST'   => '3452',
   'KRZTHPLST'   => '132',
   'KRZTOPSQL'   => '932',
   'KRZTPFOVEW'  => '796',
   'KRZTSFMTC'   => '740',
   'KRZTSNLUE'   => '312',
   'KRZTSOVEW'   => '384',
   'KRZTSTPUE'   => '224',
   'KS1BUDDY'    => '184',
   'KS1CHAT'     => '216',
   'KS1CLUINF'   => '168',
   'KS1FILESTA'  => '232',
   'KS1FTONDEM'  => '436',
   'KS1FUNCT'    => '436',
   'KS1MEETSTA'  => '520',
   'KS1PLACES'   => '408',
   'KS1POBJST'   => '260',
   'KS1PRESENC'  => '304',
   'KS1RESOLVE'  => '224',
   'KS1SCSPOS'   => '260',
   'KS1SCSSRV'   => '252',
   'KS1SCSSRVS'  => '216',
   'KS1SRVCONF'  => '404',
   'KS1SSO'      => '296',
   'KS1SVRINF'   => '340',
   'KS1TACTST'   => '3452',
   'KS1THPLST'   => '132',
   'KS3HCRQLHS'  => '76',
   'KS3HCRQLPX'  => '109',
   'KS3HSCSTOR'  => '46',
   'KS3HSFUNST'  => '115',
   'KS3HSHSTAT'  => '209',
   'KS3HSPSTOR'  => '58',
   'KS3HSWATRQ'  => '70',
   'KS3HSXFUDA'  => '124',
   'KS7CACHE'    => '476',
   'KS7CACHE1'   => '476',
   'KSAALERTS'   => '2416',
   'KSAARCHIVE'  => '585',
   'KSABDC'      => '649',
   'KSABPMDTL'   => '664',
   'KSABUFFER'   => '768',
   'KSACTS'      => '858',
   'KSADMPCNT' => '472',
   'KSADUMPS'    => '871',
   'KSAEDIFILE'  => '857',
   'KSAFSYSTEM'  => '880',
   'KSAGWYCONN'  => '1315',
   'KSAIDOCS'    => '1130',
   'KSAJOBS'     => '944',
   'KSALOCKS'    => '824',
   'KSALOGNGRP'  => '666',
   'KSALOGNINF'  => '645',
   'KSAMTSTATE'  => '1352',
   'KSANUMDTL'   => '574',
   'KSANUMSUMM'  => '596',
   'KSAOFFICE'   => '1242',
   'KSAORADTL'   => '648',
   'KSAORASUM'   => '596',
   'KSAOSP'      => '644',
   'KSAOUTPUT'   => '985',
   'KSAPERF'     => '672',
   'KSAPROCESS'  => '1088',
   'KSASERINFO'  => '340',
   'KSASLOG'     => '1008',
   'KSASLSYALT'  => '1456',
   'KSASOLALTH'  => '788',
   'KSASOLEWA'   => '592',
   'KSASPOOL'    => '760',
   'KSASYS'      => '1444',
   'KSATRANRFC'  => '1398',
   'KSATRANS'    => '1056',
   'KSAUPDATES'  => '1288',
   'KSAUSERS'    => '832',
   'KSEAVAIL' => '3244',
   'KSESTATUS' => '240',
   'KSKACTSUMM'  => '1796',
   'KSKACTVLOG'  => '1729',
   'KSKAGNTLOG'  => '704',
   'KSKAVAIL'    => '3244',
   'KSKCLIENTF'  => '876',
   'KSKCLIENTS'  => '964',
   'KSKCLIENTT'  => '2118',
   'KSKDATABAS'  => '552',
   'KSKDRVS'     => '1520',
   'KSKLIBS'     => '1100',
   'KSKNODEACT'  => '744',
   'KSKOCPNCY'   => '2112',
   'KSKPOBJST'   => '260',
   'KSKPVUDET'   => '4184',
   'KSKRPLDET'   => '2656',
   'KSKRPLSTAT'  => '3896',
   'KSKSCHEDUL'  => '1876',
   'KSKSDAGF'    => '1160',
   'KSKSERVER'   => '684',
   'KSKSESSION'  => '1440',
   'KSKSTORAGE'  => '1080',
   'KSKTAPEUSA'  => '1200',
   'KSKTAPEVOL'  => '1992',
   'KSYCONFIG'   => '1152',
   'KSYCONNECT'  => '1184',
   'KSYNODE'     => '1313',
   'KSYSUMMSTA'  => '120',
   'KSYTABLE'    => '288',
   'KUBAVAIL'    => '3244',
   'KUBCOMPDET'  => '562',
   'KUBCOMPSTA'  => '832',
   'KUBCPUCOMP'  => '3348',
   'KUBCPUTASK'  => '4284',
   'KUBCUTLRLU'  => '64',
   'KUBDBFIL'    => '288',
   'KUBDBFILSY'  => '368',
   'KUBDETSTA'   => '1456',
   'KUBDLAINP'   => '1000',
   'KUBENTERPI'  => '480',
   'KUBFILES'    => '388',
   'KUBFILESYS'  => '368',
   'KUBMKTST'    => '372',
   'KUBPOBJST'   => '260',
   'KUBSIEBSRV'  => '568',
   'KUBSIEBSTA'  => '704',
   'KUBSTATASG'  => '52',
   'KUBSTATCOM'  => '56',
   'KUBSTATCOR'  => '416',
   'KUBSTATDAT'  => '456',
   'KUBSTATEAI'  => '68',
   'KUBSTATENG'  => '56',
   'KUBSTATFLT'  => '60',
   'KUBSTATMUL'  => '84',
   'KUBSTATOBJ'  => '544',
   'KUBSTATPIM'  => '372',
   'KUBSTATREC'  => '60',
   'KUBSTATSEA'  => '56',
   'KUBSTATSUB'  => '60',
   'KUBSTATXML'  => '64',
   'KUBTASKDET'  => '1088',
   'KUBTASKSUM'  => '84',
   'KUBTUTLRLU'  => '64',
   'KUBUSERSE2'  => '64',
   'KUBUSERSES'  => '948',
   'KUD2649700'  => '3112',
   'KUD2649800'  => '658',
   'KUD2649900'  => '3646',
   'KUD3437500'  => '1858',
   'KUD3437600'  => '1658',
   'KUD4177600'  => '1498',
   'KUD4238000'  => '1600',
   'KUD5214100'  => '1030',
   'KUDAPPL00'   => '3804',
   'KUDAPPL01'   => '722',
   'KUDAPPLYPM'  => '316',
   'KUDAPPLYSN'  => '414',
   'KUDBPOOL'    => '1356',
   'KUDCUSSQLD' => '1904',
   'KUDDB2HADR'  => '1596',
   'KUDDBASE00'  => '1922',
   'KUDDBASE01'  => '1874',
   'KUDDBASE02'  => '842',
   'KUDDCSDB'    => '290',
   'KUDDIAGLOG'  => '1680',
   'KUDIPADDR'   => '166',
   'KUDLOG'      => '4932',
   'KUDSYSINFO'  => '1882',
   'KUDSYSRES'   => '696',
   'KUDTABLE'    => '304',
   'KUDTABSPC'   => '1756',
   'KUDTBLSPC'   => '1838',
   'KUXDEVIC'    => '660',
   'KUXPASALRT'  => '484',
   'KUXPASCAP'   => '3062',
   'KUXPASMGMT'  => '510',
   'KUXPASSTAT'  => '1384',
   'KUXSCRTSM' => '3544',
   'KV1HOSTAG'   => '806',
   'KV1HOSTCG'   => '527',
   'KV1HOSTMG'   => '519',
   'KV1POBJST'   => '360',
   'KV1SCHPAG'   => '941',
   'KV1STGPLAG'  => '734',
   'KV1VMACHAG'  => '950',
   'KV5BRAPP'    => '852',
   'KV5CATALOG'  => '152',
   'KV5CNTRLR'   => '852',
   'KV5DKGRAV'   => '152',
   'KV5DKGRUSE'  => '152',
   'KV5DKINGR'   => '956',
   'KV5DKPOOL'   => '56',
   'KV5DSKGRPS'  => '472',
   'KV5DUSR'     => '348',
   'KV5EVTLGDT'  => '1348',
   'KV5HYPALRT'  => '848',
   'KV5LUSE'     => '164',
   'KV5MACHINE'  => '948',
   'KV5OSTYPE'   => '152',
   'KV5POBJST'   => '360',
   'KV5PWRSTAT'  => '152',
   'KV5RAM'      => '56',
   'KV5SHUTDWN'  => '152',
   'KV5THPLST'   => '132',
   'KV5USRSSON'  => '2648',
   'KV5XD4LIC'   => '160',
   'KV5XD4MF'    => '656',
   'KV5XD4NET'   => '96',
   'KV5XD5IN'    => '1048',
   'KV5XD5SER'   => '232',
   'KV5XD5XML'   => '196',
   'KV6BCKPLNP'  => '852',
   'KV6BLSHESM'  => '1352',
   'KV6BNTSTAT'  => '896',
   'KV6BSCONFI'  => '1052',
   'KV6BSCPUCN'  => '1284',
   'KV6BSDISKC'  => '1460',
   'KV6BSETPCM'  => '1160',
   'KV6BSETPER'  => '1160',
   'KV6BSETPLS'  => '1176',
   'KV6BSETPOS'  => '1168',
   'KV6BSETPPS'  => '1172',
   'KV6BSETPSM'  => '1172',
   'KV6BSHWFWD'  => '1248',
   'KV6BSMEMAR'  => '1064',
   'KV6BSMEMUN'  => '1368',
   'KV6BSMTHRD'  => '952',
   'KV6BSSTCON'  => '1352',
   'KV6CHACNFD'  => '552',
   'KV6CHASSD'   => '980',
   'KV6CHBKERS'  => '784',
   'KV6CHBKLOS'  => '780',
   'KV6CHBKPSE'  => '760',
   'KV6CHFANHS'  => '1252',
   'KV6CHHWFWD'  => '1048',
   'KV6CHIOHSM'  => '1052',
   'KV6CHPOWER'  => '296',
   'KV6CHPSHSM'  => '1252',
   'KV6CHPSUCO'  => '752',
   'KV6CHSLDET'  => '748',
   'KV6CHSLTSM'  => '848',
   'KV6CIOCNFD'  => '952',
   'KV6CONFPRO'  => '556',
   'KV6CPUENVS'  => '880',
   'KV6CPUHESM'  => '1252',
   'KV6DCEHSUM'  => '1148',
   'KV6DSKHESM'  => '1252',
   'KV6EXPMODL'  => '956',
   'KV6FABPORT'  => '268',
   'KV6FANCONF'  => '756',
   'KV6FANHELT'  => '1452',
   'KV6FANMDCF'  => '756',
   'KV6FANSTAT'  => '752',
   'KV6FAULTS'   => '1552',
   'KV6FCPRTST'  => '1064',
   'KV6FIHESUM'  => '556',
   'KV6FIHWFWD'  => '1648',
   'KV6FILERRS'  => '584',
   'KV6FILLOSS'  => '580',
   'KV6FILPAUS'  => '560',
   'KV6FIPORTU'  => '452',
   'KV6FITMPST'  => '376',
   'KV6FIXPORT'  => '1152',
   'KV6FNHELTH'  => '956',
   'KV6FNMDLSM'  => '464',
   'KV6FSYSTEM'  => '276',
   'KV6HBACNFD'  => '2152',
   'KV6HBAHSUM'  => '1652',
   'KV6ICDCNFD'  => '956',
   'KV6INCHESM'  => '952',
   'KV6IOMDTEM'  => '580',
   'KV6LANSTAT'  => '696',
   'KV6MACPOOL'  => '464',
   'KV6MBPOWST'  => '696',
   'KV6MBTEMST'  => '712',
   'KV6MEAHESM'  => '1052',
   'KV6MEMAICS'  => '864',
   'KV6MEMTMPS'  => '1064',
   'KV6MOTHESM'  => '1152',
   'KV6NICCNFD'  => '1852',
   'KV6NICHSUM'  => '1552',
   'KV6POBJST'   => '360',
   'KV6PSUCONF'  => '656',
   'KV6PSUHLTH'  => '1056',
   'KV6PSUSTAT'  => '584',
   'KV6PWSPUSM'  => '644',
   'KV6SANEROR'  => '588',
   'KV6SANPOOL'  => '564',
   'KV6SANSTAT'  => '564',
   'KV6SERPOLD'  => '464',
   'KV6SERPRLH'  => '952',
   'KV6STCHESM'  => '1452',
   'KV6THPLST'   => '132',
   'KV6UIDSUFX'  => '564',
   'KV6VNICSTS'  => '1080',
   'KVA02STORA'  => '2936',
   'KVA03NETWO'  => '2288',
   'KVA05SECUR'  => '288',
   'KVA06FIREW'  => '372',
   'KVA08CAPAB'  => '240',
   'KVA10TOP50'  => '2460',
   'KVA11TOP50'  => '2460',
   'KVA16CPUSU'  => '240',
   'KVA17CPUDE'  => '232',
   'KVA19SYSTE'  => '80',
   'KVA20SYSTE'  => '68',
   'KVA21PAGIN'  => '76',
   'KVA22LOGIC'  => '1076',
   'KVA23WORKL'  => '904',
   'KVA24NIMRE'  => '2256',
   'KVA27PHYSI'  => '84',
   'KVA28VIRTU'  => '100',
   'KVA31PROCE'  => '80',
   'KVA32PROCE'  => '2732',
   'KVA34DISKS'  => '432',
   'KVA35PHYSI'  => '396',
   'KVA36VOLUM'  => '276',
   'KVA37LOGIC'  => '1204',
   'KVA38FILES'  => '1028',
   'KVA40NETWO'  => '1527',
   'KVA41NETWO'  => '4008',
   'KVA42NETWO'  => '996',
   'KVA43INTER'  => '76',
   'KVA44INTER'  => '180',
   'KVA45TCP'    => '88',
   'KVA49DEFIN'  => '1636',
   'KVA50ACTIV'  => '1680',
   'KVA51DEVIC'  => '528',
   'KVA51MPIOS'  => '528',
   'KVA52MPIOA'  => '528',
   'KVA53MPOOL'  => '144',
   'KVA53SEA'    => '608',
   'KVA54QOS'    => '808',
   'KVA55NPIVM'  => '656',
   'KVA56NPIVF'  => '152',
   'KVA56TADDM'  => '152',
   'KVAFC_STAT'  => '408',
   'KVAPOBJST'   => '260',
   'KVLCPC'      => '164',
   'KVLLGR'      => '268',
   'KVLSCSI'     => '608',
   'KVLSSI'      => '124',
   'KVMALARMS'   => '786',
   'KVMAEVENTS'  => '192',
   'KVMATASKS'   => '852',
   'KVMCLTDRSF'  => '1548',
   'KVMCLTRDST'  => '906',
   'KVMCLTRRPS'  => '622',
   'KVMCLTRSRV'  => '588',
   'KVMCLTRVMS'  => '556',
   'KVMCLTVAPS'  => '818',
   'KVMCLUSTRT'  => '872',
   'KVMDAG'      => '169',
   'KVMDCNETS'   => '506',
   'KVMDCTRS'    => '370',
   'KVMDIRE'     => '118',
   'KVMDRCLUST'  => '464',
   'KVMDSHSD'    => '548',
   'KVMDSTORES'  => '1284',
   'KVMDVPGRPS'  => '586',
   'KVMDVSWTCH'  => '334',
   'KVMDVUPLNK'  => '830',
   'KVMESXPOS'   => '360',
   'KVMIRAEVNT'  => '1936',
   'KVMNETSERV'  => '510',
   'KVMNETVM'    => '710',
   'KVMNVSWITC'  => '514',
   'KVMPOBJST'   => '360',
   'KVMRSPOOLC'  => '612',
   'KVMRSPOOLG'  => '568',
   'KVMRSPOOLM'  => '612',
   'KVMSERVERC'  => '268',
   'KVMSERVERD'  => '568',
   'KVMSERVERE'  => '1876',
   'KVMSERVERG'  => '2288',
   'KVMSERVERM'  => '340',
   'KVMSERVERN'  => '804',
   'KVMSERVRDS'  => '680',
   'KVMSRVHBAS'  => '644',
   'KVMSVRHLTH'  => '752',
   'KVMSRVRSAN'  => '460',
   'KVMSRVVSWI'  => '464',
   'KVMSTOPO'    => '798',
   'KVMSVMDSUT'  => '528',
   'KVMSVRHLTH'  => '764',
   'KVMTASKS'    => '1948',
   'KVMTHPLST'   => '132',
   'KVMTOPEVNT'  => '470',
   'KVMTOPO'     => '798',
   'KVMVCENTER'  => '476',
   'KVMVM_CPU'   => '584',
   'KVMVM_DISK'  => '960',
   'KVMVM_GEN'   => '1760',
   'KVMVM_MEM'   => '632',
   'KVMVM_NET'   => '1072',
   'KVMVM_PART'  => '576',
   'KVMVMDKPRF'  => '314',
   'KVMVMDSUTL'  => '588',
   'KVMVMORPDI'  => '752',
   'KVMVMSNAPS'  => '652',
   'KVMVSWITCH'  => '414',
   'KXAAGENCON'  => '436',
   'KXAAPPDE5'   => '5289',
   'KXAAPPDET'   => '5279',
   'KXAAPPDETS'  => '2308',
   'KXAAPPSU5'   => '442',
   'KXAAPPSUM'   => '442',
   'KXAAPPSUMM'  => '634',
   'KXACLSDS'    => '169',
   'KXACLSPOS'   => '360',
   'KXACLSSS'    => '918',
   'KXACONFI5'   => '2090',
   'KXACONFIG'   => '2090',
   'KXAELOGCLS'  => '2418',
   'KXAELOGXA5'  => '2418',
   'KXAELOGXA6'  => '2418',
   'KXAFRMDS'    => '169',
   'KXAFRMSUMM'  => '634',
   'KXAICASES5'  => '702',
   'KXAICASESD'  => '702',
   'KXAIMANE5'   => '410',
   'KXAIMANET'   => '410',
   'KXALICDETS'  => '336',
   'KXALICENS5'  => '426',
   'KXALICENSE'  => '426',
   'KXAMETAFR5'  => '602',
   'KXAMETAFRA'  => '602',
   'KXANTSR5'    => '933',
   'KXANTSRV'    => '933',
   'KXANTSRV5'   => '943',
   'KXANTSRVO'   => '943',
   'KXAPOBJST'   => '360',
   'KXAPROCDE5'  => '942',
   'KXAPROCDET'  => '942',
   'KXARFMPOS'   => '360',
   'KXASECURE0'  => '446',
   'KXASECURE5'  => '446',
   'KXASESSDE5'  => '1862',
   'KXASESSDET'  => '1862',
   'KXASESSSU5'  => '474',
   'KXASESSSUM'  => '474',
   'KXASRVCON'   => '918',
   'KXASRVDETS'  => '2082',
   'KXATACTST'   => '3452',
   'KXATHPLST'   => '132',
   'KXAUSERDE5'  => '606',
   'KXAUSERDET'  => '606',
   'KXAUSERSU5'  => '410',
   'KXAUSERSUM'  => '410',
   'KXAWGSUMM'   => '634',
   'KXAWMIFRM'   => '359',
   'KXAWORGRP'   => '653',
   'KXAWRKDETS'  => '1798',
   'KXAXA5DS'    => '169',
   'KXAXA5POS'   => '360',
   'KXAXA6DS'    => '169',
   'KXAXA6POS'   => '360',
   'KXAXAPST5'   => '1360',
   'KXAXAPSTA'   => '1360',
   'KXAXENAPP0'  => '770',
   'KXAXENAPPC'  => '180',
   'KXAZONSUMM'  => '889',
   'KXIATTRI21'  => '276',
   'KXIATTRI34'  => '732',
   'KXIATTRIB4'  => '814',
   'KXIHCTRLDM'  => '336',
   'KXIHHCPUSN'  => '640',
   'KXIHOSTPBD'  => '345',
   'KXIHOSTPCH'  => '445',
   'KXIHOSTPIF'  => '889',
   'KXIHSTDETA'  => '1837',
   'KXIHVHODET'  => '1833',
   'KXIHVVMSUB'  => '1309',
   'KXIPBD'      => '376',
   'KXIPMCHANG'  => '320',
   'KXIPOBJST'   => '360',
   'KXIPOOL'     => '620',
   'KXIPPATCH'   => '412',
   'KXISRHJOIN'  => '590',
   'KXISRS'      => '293',
   'KXITHPLST'   => '132',
   'KXIVBD'      => '1116',
   'KXIVDI'      => '912',
   'KXIXENEVTS'  => '1280',
   'KXIXENMFND'  => '353',
   'KXIXHVDS'    => '169',
   'KXIXHVPOS'   => '360',
   'KY8ACDS'     => '169',
   'KY8ACPOS'    => '360',
   'KY8AHUA'     => '1030',
   'KY8AHUB'     => '1014',
   'KY8AHUDS'    => '169',
   'KY8AHUPOS'   => '360',
   'KY8AHUS'     => '1378',
   'KY8BLRA'     => '1030',
   'KY8BLRB'     => '1014',
   'KY8BLRDS'    => '169',
   'KY8BLRPOS'   => '360',
   'KY8BLRS'     => '700',
   'KY8CDUA'     => '1030',
   'KY8CDUB'     => '1014',
   'KY8CDUDS'    => '169',
   'KY8CDUPOS'   => '360',
   'KY8CDUS'     => '294',
   'KY8CHPA'     => '1030',
   'KY8CHPB'     => '1014',
   'KY8CHPDS'    => '169',
   'KY8CHPPOS'   => '360',
   'KY8CHPS'     => '338',
   'KY8CHRS'     => '688',
   'KY8CRACA'    => '1030',
   'KY8CRACB'    => '1014',
   'KY8CRACS'    => '556',
   'KY8FMA'      => '1030',
   'KY8FMB'      => '1014',
   'KY8FMDS'     => '169',
   'KY8FMPOS'    => '360',
   'KY8FMS'      => '262',
   'KY8GENA'     => '1030',
   'KY8GENB'     => '1014',
   'KY8GENDS'    => '169',
   'KY8GENPOS'   => '360',
   'KY8GENS'     => '566',
   'KY8HXUA'     => '1030',
   'KY8HXUB'     => '1014',
   'KY8HXUDS'    => '169',
   'KY8HXUPOS'   => '360',
   'KY8HXUS'     => '262',
   'KY8JMXATTR'  => '2096',
   'KY8JMXNOTI'  => '2420',
   'KY8MTRA'     => '1030',
   'KY8MTRB'     => '1014',
   'KY8MTRDS'    => '169',
   'KY8MTRPOS'   => '360',
   'KY8MTRS'     => '326',
   'KY8OTHA'     => '1030',
   'KY8OTHB'     => '1014',
   'KY8OTHDS'    => '169',
   'KY8OTHPOS'   => '360',
   'KY8PDUA'     => '1030',
   'KY8PDUB'     => '1014',
   'KY8PDUBS'    => '674',
   'KY8PDUDS'    => '169',
   'KY8PDUPOS'   => '360',
   'KY8PDUPS'    => '524',
   'KY8PDUS'     => '278',
   'KY8POBJST'   => '360',
   'KY8RPTAC'    => '2084',
   'KY8RPTAHU'   => '2866',
   'KY8RPTBKR'   => '566',
   'KY8RPTBLR'   => '2274',
   'KY8RPTCDU'   => '2012',
   'KY8RPTCHP'   => '2016',
   'KY8RPTCHR'   => '2298',
   'KY8RPTFM'    => '1984',
   'KY8RPTGEN'   => '2000',
   'KY8RPTHXU'   => '2004',
   'KY8RPTINFO'  => '366',
   'KY8RPTMTR'   => '1996',
   'KY8RPTPDU'   => '1984',
   'KY8RPTPNL'   => '364',
   'KY8RPTSNS'   => '2008',
   'KY8RPTUPS'   => '2032',
   'KY8SNSA'     => '1030',
   'KY8SNSB'     => '1014',
   'KY8SNSDS'    => '169',
   'KY8SNSPOS'   => '360',
   'KY8SNSS'     => '800',
   'KY8THPLST'   => '132',
   'KY8UPSA'     => '1030',
   'KY8UPSB'     => '1014',
   'KY8UPSDS'    => '169',
   'KY8UPSPOS'   => '360',
   'KY8UPSS'     => '570',
   'KY9ACDS'     => '169',
   'KY9ACPOS'    => '360',
   'KY9AHUA'     => '1030',
   'KY9AHUB'     => '1014',
   'KY9AHUDS'    => '169',
   'KY9AHUPOS'   => '360',
   'KY9AHUS'     => '1378',
   'KY9BLRA'     => '1030',
   'KY9BLRB'     => '1014',
   'KY9BLRDS'    => '169',
   'KY9BLRPOS'   => '360',
   'KY9BLRS'     => '700',
   'KY9CDUA'     => '1030',
   'KY9CDUB'     => '1014',
   'KY9CDUDS'    => '169',
   'KY9CDUPOS'   => '360',
   'KY9CDUS'     => '294',
   'KY9CHPA'     => '1030',
   'KY9CHPB'     => '1014',
   'KY9CHPDS'    => '169',
   'KY9CHPPOS'   => '360',
   'KY9CHPS'     => '338',
   'KY9CHRS'     => '688',
   'KY9CRACA'    => '1030',
   'KY9CRACB'    => '1014',
   'KY9CRACS'    => '556',
   'KY9FMA'      => '1030',
   'KY9FMB'      => '1014',
   'KY9FMDS'     => '169',
   'KY9FMPOS'    => '360',
   'KY9FMS'      => '262',
   'KY9GENA'     => '1030',
   'KY9GENB'     => '1014',
   'KY9GENDS'    => '169',
   'KY9GENPOS'   => '360',
   'KY9GENS'     => '566',
   'KY9HXUA'     => '1030',
   'KY9HXUB'     => '1014',
   'KY9HXUDS'    => '169',
   'KY9HXUPOS'   => '360',
   'KY9HXUS'     => '262',
   'KY9MTRA'     => '1030',
   'KY9MTRB'     => '1014',
   'KY9MTRDS'    => '169',
   'KY9MTRPOS'   => '360',
   'KY9MTRS'     => '326',
   'KY9OTHA'     => '1030',
   'KY9OTHB'     => '1014',
   'KY9OTHDS'    => '169',
   'KY9OTHPOS'   => '360',
   'KY9PDUA'     => '1030',
   'KY9PDUB'     => '1014',
   'KY9PDUBS'    => '674',
   'KY9PDUDS'    => '169',
   'KY9PDUPOS'   => '360',
   'KY9PDUPS'    => '524',
   'KY9PDUS'     => '278',
   'KY9POBJST'   => '360',
   'KY9RPTAC'    => '2084',
   'KY9RPTAHU'   => '2866',
   'KY9RPTBKR'   => '566',
   'KY9RPTBLR'   => '2274',
   'KY9RPTCDU'   => '2012',
   'KY9RPTCHP'   => '2016',
   'KY9RPTCHR'   => '2298',
   'KY9RPTFM'    => '1992',
   'KY9RPTGEN'   => '2000',
   'KY9RPTHXU'   => '2004',
   'KY9RPTINFO'  => '366',
   'KY9RPTMTR'   => '1996',
   'KY9RPTPDU'   => '1984',
   'KY9RPTPNL'   => '364',
   'KY9RPTSNS'   => '2008',
   'KY9RPTUPS'   => '2032',
   'KY9SNSA'     => '1030',
   'KY9SNSB'     => '1014',
   'KY9SNSDS'    => '169',
   'KY9SNSPOS'   => '360',
   'KY9SNSS'     => '800',
   'KY9THPLST'   => '132',
   'KY9UPSA'     => '1030',
   'KY9UPSB'     => '1014',
   'KY9UPSDS'    => '169',
   'KY9UPSPOS'   => '360',
   'KY9UPSS'     => '570',
   'KYJAPHLTH'   => '980',
   'KYJAPMONCF'  => '1748',
   'KYJAPSRV'    => '1148',
   'KYJAPSST'    => '1516',
   'KYJDATAS'    => '1256',
   'KYJDCMSG'    => '1376',
   'KYJEJB'      => '992',
   'KYJGCACT'    => '712',
   'KYJGCAF'     => '716',
   'KYJGCCYC'    => '756',
   'KYJJCACP'    => '1060',
   'KYJJDKJVM'   => '1704',
   'KYJJDKMEM'   => '696',
   'KYJJDKOS'    => '1456',
   'KYJJDKTHR'   => '1196',
   'KYJJMSSUM'   => '952',
   'KYJJTARES'   => '932',
   'KYJLOGANAL'  => '1040',
   'KYJPREV'     => '676',
   'KYJREQHIS'   => '952',
   'KYJREQSEL'   => '1364',
   'KYJREQUEST'  => '1568',
   'KYJSDBCON'   => '944',
   'KYJSEJB'     => '1124',
   'KYJSERVLT'   => '992',
   'KYJSJTASUM'  => '680',
   'KYJSWEBCNT'  => '688',
   'KYJWEBAPP'   => '832',
   'KYJWLCCPL'   => '856',
   'KYJWLDBCON'  => '872',
   'KYJWLEJB'    => '1328',
   'KYJWLEJBC'   => '940',
   'KYJWLJMSS'   => '1060',
   'KYJWLJTA'    => '872',
   'KYJWLSRVLT'  => '1636',
   'KYJWLWEBAP'  => '1268',
   'KYNALARMM'   => '1000',
   'KYNAPHLTH'   => '996',
   'KYNAPP'      => '1096',
   'KYNAPSRV'    => '1560',
   'KYNAPSST'    => '1692',
   'KYNCACHE'    => '836',
   'KYNCACHT'    => '1364',
   'KYNCLICOM'   => '1192',
   'KYNCNTROP'   => '872',
   'KYNCONTNR'   => '864',
   'KYNDATAS'    => '1224',
   'KYNDBCONP'   => '1100',
   'KYNDCMSG'    => '1384',
   'KYNDCSSTK'   => '1088',
   'KYNDURSUB'   => '1488',
   'KYNEJB'      => '1028',
   'KYNGCACT'    => '752',
   'KYNGCAF'     => '592',
   'KYNGCCYC'    => '632',
   'KYNGZCAT'    => '360',
   'KYNGZCONT'   => '276',
   'KYNGZGRPLC'  => '144',
   'KYNGZMAP'    => '316',
   'KYNGZPOOL'   => '180',
   'KYNGZRID'    => '360',
   'KYNGZSERV'   => '804',
   'KYNGZSHARD'  => '456',
   'KYNHAMGMT'   => '792',
   'KYNJ2C'      => '1144',
   'KYNJMSSUM'   => '944',
   'KYNLOGANAL'  => '1044',
   'KYNLPORT'    => '1444',
   'KYNMECOM'    => '976',
   'KYNMSGENG'   => '948',
   'KYNMSGQUE'   => '1276',
   'KYNPREV'     => '588',
   'KYNREQHIS'   => '964',
   'KYNREQSEL'   => '1248',
   'KYNREQUEST'  => '1488',
   'KYNSCHED'    => '1068',
   'KYNSERVLT'   => '1296',
   'KYNSERVS'    => '1188',
   'KYNSVCCOMP'  => '676',
   'KYNSVCOMEL'  => '1772',
   'KYNTHRDP'    => '852',
   'KYNTOPICSP'  => '1260',
   'KYNTRANS'    => '1016',
   'KYNWEBSGW'   => '940',
   'KYNWEBSVC'   => '1088',
   'KYNWLMCL'    => '616',
   'KYNWLMSR'    => '716',
   'KYNWMQCL'    => '960',
   'KYNWMQLINK'  => '976',
   'KYNWPLETS'   => '856',
   'KYNWPPAGE'   => '840',
   'KYNWPTALS'   => '888',
   'KYNXDCG'     => '956',
   'KYNXDGE'     => '1388',
   'KYNXDODR'    => '1988',
   'KYNXDSPV'    => '568',
   'KYNXDSRV'    => '556',
   'KZABPCHECK' => '4192',
   'KZEBLADE'    => '493',
   'KZECPC'      => '611',
   'KZEECCDS'    => '968',
   'KZEENSEMBL'  => '542',
   'KZELPAR'     => '1210',
   'KZEMVMVSV'   => '1048',
   'KZEPERFPOL'  => '800',
   'KZEPOBJST'   => '360',
   'KZEPRSMVH'   => '344',
   'KZEPVMVH'    => '420',
   'KZEPVMVSV'   => '1205',
   'KZESVCLASS'  => '728',
   'KZETACTST'   => '3452',
   'KZETHPLST'   => '132',
   'KZEUPLINK'   => '564',
   'KZEVNET'     => '628',
   'KZEWKLOAD'   => '904',
   'KZEWKLVSV'   => '1628',
   'KZEXVMVH'    => '408',
   'KZEXVMVSV'   => '1076',
   'KZEZBX'      => '376',
   'KZEZVMVH'    => '452',
   'KZEZVMVSV'   => '1269',
   'LCHANNEL'    => '324',
   'LCU'         => '886',
   'LGB_POOL'    => '136',
   'LKDP_CF'     => '184',
   'LIMS_PARM'   => '156',
   'LNXALLUSR'   => '152',
   'LNXCPU'      => '156',
   'LNXCPUAVG'   => '180',
   'LNXCPUCON'   => '300',
   'LNXDISK'     => '488',
   'LNXDSKIO'    => '212',
   'LNXDU'       => '204',
   'LNXFILE'       => '5116',
   'LNXFILPAT'   => '1624',
   'LNXGROUP'    => '144',
   'LNXIOEXT'    => '248',
   'LNXIPADDR'   => '548',
   'LNXLOGIN'    => '524',
   'LNXMACHIN'   => '828',
   'LNXNET'      => '317',
   'LNXNFS'      => '324',
   'LNXOSCON'    => '440',
   'LNXPING'     => '216',
   'LNXPROC'     => '1324',
   'LNXPUSR'     => '1416',
   'LNXRPC'      => '152',
   'LNXSOCKD'    => '312',
   'LNXSOCKS'    => '132',
   'LNXSWPRT'    => '148',
   'LNXSYS'      => '312',
   'LNXVM'       => '336',
   'LOCALTIME'   => 112,
   'LPARINFO'    => '364',
   'LPCLUST'     => '247',
   'LTCGENE64'   => '280',
   'LTCGENED32'  => '280',
   'LTCGENED64'  => '280',
   'LTCGENERIC'  => '280',
   'LTERMS'      => '119',
   'LTFGENE64'   => '284',
   'LTFGENED32'  => '292',
   'LTFGENED64'  => '292',
   'LTFGENERIC'  => '280',
   'M5ZFSDCI'    => '115',
   'M5ZFSKER'    => '61',
   'M5ZFSMCI'    => '172',
   'M5ZFSSTI'    => '460',
   'M5ZFSUCA'    => '477',
   'M5ZFSUCD'    => '222',
   'MADDSPC'     => '1143',
   'MCFCLIENT'   => '210',
   'MCFPATH'     => '1132',
   'MCFPOLCY'    => '122',
   'MCFSMVS'     => '88',
   'MCFSTRCT'    => '52',
   'MCFSYS'      => '367',
   'MDASD_DEV'   => '103',
   'MDASD_GRP'   => '148',
   'MDASD_SYS'   => '52',
   'MDCACHE'     => '556',
   'MGLBLENQ'    => '595',
   'MOUNTS2'     => '153',
   'MQCONN'      => '115',
   'MRESGRP'     => '124',
   'MRPTCLS'     => '184',
   'MSC_LLNK'    => '148',
   'MSC_PLNK'    => '144',
   'MSDB'        => '179',
   'MSDBF'       => '128',
   'MSEADACP'    => '896',
   'MSEADCAH'    => '700',
   'MSEAF'       => '112',
   'MSEASSIT'    => '856',
   'MSEASSTDB'   => '804',
   'MSEASYNC'    => '344',
   'MSEAVSERV'   => '136',
   'MSECFA'      => '208',
   'MSECONFA'    => '184',
   'MSEDAG'      => '612',
   'MSEDB'       => '592',
   'MSEDBINS'    => '708',
   'MSEDS'       => '292',
   'MSEIS'       => '384',
   'MSEISCLI'    => '184',
   'MSEISPRI'    => '1064',
   'MSEISPUB'    => '1028',
   'MSEISPUR'    => '752',
   'MSEISSTR'    => '2920',
   'MSELOTUS'    => '144',
   'MSEMANFA'    => '108',
   'MSEMBXD'     => '1676',
   'MSEMCD'      => '212',
   'MSEMREPS'    => '116',
   'MSEMRSPM'    => '740',
   'MSEMTA'      => '296',
   'MSEMTAC'     => '552',
   'MSENLBS'     => '152',
   'MSEOWA'      => '200',
   'MSEPAA'      => '124',
   'MSEPFLDD'    => '1276',
   'MSEPRXY'     => '116',
   'MSERBAC'     => '184',
   'MSERBS'      => '544',
   'MSERCACH'    => '488',
   'MSEREACH'    => '892',
   'MSEREPL'     => '148',
   'MSERFA'      => '128',
   'MSERMS'      => '472',
   'MSERPCCA'    => '152',
   'MSESERVR'    => '2744',
   'MSESFA'      => '128',
   'MSESGRPD'    => '524',
   'MSESIDAG'    => '152',
   'MSESMTPR'    => '620',
   'MSESMTPS'    => '612',
   'MSESRVCD'    => '488',
   'MSESTOINT'   => '760',
   'MSESTRDR'    => '808',
   'MSETRDB'     => '1008',
   'MSETRDMP'    => '140',
   'MSETRQUE'    => '616',
   'MSETRRUL'    => '512',
   'MSETRSR'     => '432',
   'MSFSSS'      => '244',
   'MSMBSCS'     => '480',
   'MSMQIS'      => '244',
   'MSMQQUE'     => '424',
   'MSMQSESS'    => '312',
   'MSMQSVC'     => '252',
   'MSRTOPO'     => '480',
   'MSRVCLS'     => '200',
   'MSRVDEF'     => '134',
   'MSSWFA'      => '114',
   'MVSTOR64'    => '1260',
   'MWFAENQ'     => '160',
   'MWFAIO'      => '349',
   'MWLMPR'      => '83',
   'MXCFGRP'     => '124',
   'MXCFMBR'     => '88',
   'MXCFPATH'    => '100',
   'MXCFSSTA'    => '108',
   'MXCFSYS'     => '126',
   'NETSEGMT'    => '180',
   'NETWRKIN'    => '476',
   'NNTPCMD'     => '328',
   'NNTPSRV'     => '312',
   'NTBIOSINFO'  => '656',
   'NTCACHE'     => '340',
   'NTCOMPINFO'  => '1232',
   'NTDEVDEP'    => '668',
   'NTDEVICE'    => '1148',
   'NTEVTLOG'    => '3132',
   'NTFLCHG'     => '1532',
   'NTFLTREND'   => '1584',
   'NTIPADDR'    => '872',
   'NTJOBOBJD'   => '692',
   'NTLOGINFO'   => '1256',
   'NTMEMORY'    => '348',
   'NTMNTPT'     => '624',
   'NTNETWPORT'  => '772',
   'NTNETWRKIN'  => '992',
   'NTPAGEFILE'  => '552',
   'NTPRINTER'   => '2424',
   'NTPROCESS'   => '960',
   'NTPROCINFO'  => '452',
   'NTPROCRSUM'  => '340',
   'NTPROCSSR'   => '192',
   'NTPRTJOB'    => '1436',
   'NTREDIRECT'  => '476',
   'NTSERVERQ'   => '248',
   'NTSERVICE'   => '1472',
   'NTSVCDEP'    => '680',
   'OEKERNL2'    => '137',
   'OLDS'        => '186',
   'OPERALRT'    => '177',
   'OPERSYS'     => '176',
   'OPS2'        => '80',
   'OSAMSUBP'    => '100',
   'OTMAGROUP'   => '83',
   'OTMASTATUS'  => '282',
   'OTMATMEM'    => '272',
   'OTMATPIPE'   => '167',
   'OUSERS2'     => '121',
   'PAGEDS'      => '343',
   'PAGING'      => '514',
   'POOLUTIL'    => '320',
   'PRINTQ'      => '576',
   'PROCESSIO'   => '704',
   'PROCESSOR'   => '302',
   'PSBS'        => '282',
   'PTKSTAT'     => '148',
   'QM_APAI'     => '380',
   'QM_APQL'     => '484',
   'QM_APTL'     => '416',
   'QMACTLOG'    => '1530',
   'QMCH_DATA'   => '976',
   'QMCH_LH'     => '956',
   'QMCH_STAT'   => '764',
   'QMCHAN_ST'   => '1608',
   'QMCHAN_SUM'  => '736',
   'QMCHANIN'    => '312',
   'QMCHANNEL'   => '1044',
   'QMCHANS'     => '1632',
   'QMCONNAPP'   => '1136',
   'QMCONNOBJ'   => '1052',
   'QMCURSTAT'   => '2416',
   'QMDSPUSAGE'  => '344',
   'QMERRLOG'    => '3916',
   'QMEVENTC'    => '436',
   'QMEVENTH'    => '2756',
   'QMEVENTL'    => '1668',
   'QMLHBM'      => '432',
   'QMLHLM'      => '760',
   'QMLHMM'      => '488',
   'QMLHTM'      => '436',
   'QMLSSTATUS'  => '1192',
   'QMMQIACCT'   => '1204',
   'QMMQICDET'   => '336',
   'QMMQIMDET'   => '232',
   'QMMQISTAT'   => '940',
   'QMMSG_STAT'  => '604',
   'QMPS_LH'     => '336',
   'QMQ_ACCT'    => '880',
   'QMQ_DATA'    => '932',
   'QMQ_HDL_ST'  => '1036',
   'QMQ_LH'      => '720',
   'QMQ_QU_ST'   => '364',
   'QMQ_STAT'    => '708',
   'QMQUEUE'     => '932',
   'QMQUEUES'    => '844',
   'QSG_CFBKUP'  => '212',
   'QSG_CFCONN'  => '304',
   'QSG_CFSTR'   => '556',
   'QSG_CHANS'   => '240',
   'QSG_QMGR'    => '304',
   'QSG_QUEUES'  => '220',
   'READHIST'    => '1224',
   'REALACT'     => '2261',
   'REALENC'     => '1821',
   'REALRSUM'    => '1428',
   'REALSQLC'    => '92',
   'REALSQLS'    => '565',
   'REALSTOR'    => '1376',
   'REALTHDA'    => '1264',
   'RECONDS'     => '144',
   'RLS'         => '392',
   'RMMCDS'      => '208',
   'RMMCFG'      => '336',
   'RMMSUM'      => '405',
   'RTA_GNT'     => '135',
   'RTA_LINT'    => '77',
   'S3VTCACHPC'  => '136',
   'S3VTCHPGRP'  => '144',
   'S3VTCLUSTR'  => '132',
   'S3VTTPVOLC'  => '128',
   'SMS_CONFIG'  => '451',
   'SMS_DAT_CL'  => '289',
   'SMS_MAN_CL'  => '273',
   'SMS_ST_CL'   => '245',
   'SMS_ST_GRP'  => '506',
   'SMS_SYSTEM'  => '41',
   'SMTPSRV'     => '368',
   'SPINLOCK'    => '132',
   'SQAPPCS1'    => '424',
   'SQAPPCS2'    => '429',
   'SQCOLDS1'    => '132',
   'SQCOLDS2'    => '222',
   'SQFPPGMS'    => '112',
   'SQLTERMS'    => '260',
   'SQOTMAS1'    => '132',
   'SQOTMAS2'    => '132',
   'SQTRANS'     => '128',
   'ST_GRP_STA'  => '71',
   'SUBPOOLS'    => '152',
   'SUMTRANS'    => '132',
   'SUSLOCK'     => '110',
   'SVCDET'      => '304',
   'SYM_CONFIG'  => '262',
   'SYM_DIR_OV'  => '74',
   'SYM_DSK_DR'  => '327',
   'SYM_DSK_DV'  => '116',
   'SYM_SSIDS'   => '116',
   'SYSCPUUTIL'  => '3890',
   'T3AGNTMSGS'  => '1668',
   'T3ISMPHS'    => '708',
   'T3ISMPHSE'   => '808',
   'T3ISMPHSEA'  => '808',
   'T3PBSTAT' => '948',
   'T3ISMPROFS'  => '552',
   'T3SNAGENT'   => '688',
   'T3SNAPPL'    => '500',
   'T3SNCLIENT'  => '628',
   'T3SNCLTAGT'  => '688',
   'T3SNSERVER'  => '688',
   'T3SNSVRAGT'  => '688',
   'T3SNTRANS'   => '628',
   'T4AGNTMSGS'  => '1668',
   'T4APPCS'     => '542',
   'T4SRVCS'     => '684',
   'T4SUBTXCS'   => '860',
   'T4SUBTXINS'  => '2263',
   'T4TXCS'      => '958',
   'T4TXINS'     => '2237',
   'T5AGNTMSGS'  => '1668',
   'T5APPCS'     => '480',
   'T5APPSM'     => '452',
   'T5CLNTCS'    => '720',
   'T5DEPOTSTS'  => '64',
   'T5SRVCS'     => '648',
   'T5SSLALRCS'  => '358',
   'T5SUBTXCS'   => '1100',
   'T5SUBTXINS'  => '4893',
   'T5TCPSTAT'   => '1176',
   'T5TGAT'      => '1252',
   'T5TXCS'      => '1214',
   'T5TXINS'     => '5241',
   'T5USRSS'     => '704',
   'T6AGNTMSGS'  => '1668',
   'T6APPCS'     => '586',
   'T6CLNTOT'    => '604',
   'T6PBEVENT'   => '2752',
   'T6PBSTAT'    => '928',
   'T6SUBTXCS'   => '684',
   'T6SUBTXINS'  => '2347',
   'T6TXCS'      => '1002',
   'T6TXINS'     => '2289',
   'T6TXSM'      => '752',
   'TAPE_DEV'    => '87',
   'TAPE_GRP'    => '260',
   'TAPEDRVS'    => '58',
   'TCONOVER'    => '962',
   'TCONPKG'     => '537',
   'TCONSTMT'    => '624',
   'TCPSDATA'    => '528',
   'TCPSTATS'    => '252',
   'TCPUDATA'    => '304',
   'TDB2CONN'    => '465',
   'TDS_ARRAY'   => '99',
   'TDS_CONFIG'  => '178',
   'TDS_EXPOOL'  => '231',
   'TDS_RANK'    => '196',
   'TDS_SSIDS'   => '138',
   'THDDF64'     => '581',
   'THREAD2'     => '2070',
   'TINST'       => '3582',
   'TINSTCXT'    => '912',
   'TINSTINT'    => '4362',
   'TOPUSER'     => '2606',
   'TRAN'        => '271',
   'TRANS'       => '280',
   'TRF_CLASS'   => '84',
   'TRF_DLIS'    => '156',
   'TUPERIODS'   => '92',
   'UDPSTATS'    => '236',
   'ULLOGENT'    => '2864',
   'ULMONLOG'    => '1988',
   'UNIXALLUSR'  => '160',
   'UNIXAMS'     => '212',
   'UNIXCPU'     => '348',
   'UNIXDCSTAT'  => '184',
   'UNIXDEVIC'   => '560',
   'UNIXDISK'    => '1572',
   'UNIXDPERF'   => '832',
   'UNIXDUSERS'  => '1668',
   'UNIXFILPAT'  => '1624',
   'UNIXGROUP'   => '136',
   'UNIXIPADDR'  => '548',
   'UNIXLPAR'    => '1556',
   'UNIXLVOLUM'  => '1240',
   'UNIXMACHIN'  => '516',
   'UNIXMEM'     => '448',
   'UNIXNET'     => '1600',
   'UNIXNFS'     => '492',
   'UNIXOS'      => '980',
   'UNIXPING'    => '868',
   'UNIXPS'      => '2736',
   'UNIXPVOLUM'  => '552',
   'UNIXSOLZON'  => '564',
   'UNIXTCP'     => '104',
   'UNIXTOPCPU'  => '1844',
   'UNIXTOPMEM'  => '1864',
   'UNIXUSER'    => '540',
   'UNIXVOLGRP'  => '336',
   'UNIXWPARCP'  => '432',
   'UNIXWPARFS'  => '1616',
   'UNIXWPARIN'  => '5504',
   'UNIXWPARNE'  => '1360',
   'UNIXWPARPM'  => '400',
   'UNXPRINTQ'   => '288',
   'URESPTM'     => '124',
   'UTCTIME'  => 112,
   'VCF_GROUP'   => '316',
   'VCMLCPU'     => '124',
   'VCMLPAR'     => '148',
   'VDB2LKCONF'  => '694',
   'VDISK'       => '311',
   'VDPTHDET'    => '636',
   'VLCONFLICT'  => '460',
   'VMCPDEV'     => '160',
   'VMDEV'       => '224',
   'VMHIPER'     => '264',
   'VMLXAPPL'    => '880',
   'VMMEMORY'    => '128',
   'VMPROCSSR'   => '196',
   'VMSYSTEM'    => '504',
   'VMSYSTEM2'   => '588',
   'VMWAIT'      => '208',
   'VMWORK'      => '760',
   'VOL_SY_STA'  => '48',
   'VSAM'        => '366',
   'VSAMOSAM'    => '144',
   'VSAMSUBP'    => '280',
   'VSMCHANNL'   => '71',
   'VSMCONFIG'   => '124',
   'VSMQUEUED'   => '153',
   'VSMRTDSTAT'  => '139',
   'VSMSTATUS'   => '136',
   'VSMSUBPOOL'  => '91',
   'VSOAREAS'    => '172',
   'VSODSPCS'    => '184',
   'VSWITCH'     => '662',
   'VTHDSTAT'    => '152',
   'VTSCACHE'    => '93',
   'VTSCAPACTY'  => '253',
   'VTSCOMPOS'   => '136',
   'VTSDEVICES'  => '200',
   'VTSOVRVIEW'  => '129',
   'VTSPHYSDEV'  => '94',
   'VTSVIRTDEV'  => '144',
   'WEBSVC'      => '392',
   'WSS'         => '291',
   'WTLOGCLDSK'  => '652',
   'WTMEMORY'    => '388',
   'WTOBJECTS'   => '240',
   'WTPHYSDSK'   => '320',
   'WTPROCESS'   => '1028',
   'WTSERVER'    => '364',
   'WTSERVERQ'   => '220',
   'WTSYSTEM'    => '900',
   'WTTHREAD'    => '328',
   'XRF'         => '228',
);

# current search list
# KUDAGINF
# 'KSASLOG'  => '',

my %newtabsizex;

my $advi = -1;                  # capture advisories
my @advonline = ();
my @advsit = ();
my @advimpact = ();
my @advcode = ();
my %advx = ();
my $rptkey = "";
my $max_impact = 0;

my %advtextx = ();
my $advkey = "";
my $advtext = "";
my $advline;
my %advgotx = ();
my %advrptx = ();

while (<main::DATA>)
{
  $advline = $_;
  $advline =~ s/\x0d//g if $gWin == 0;
  if ($advkey eq "") {
     chomp $advline;
     $advkey = $advline;
     next;
  }
  if (length($advline) >= 15) {
     if ((substr($advline,0,10) eq "EVENTAUDIT") or (substr($advline,0,11) eq "EVENTREPORT")){
        $advtextx{$advkey} = $advtext;
        chomp $advline;
        $advkey = $advline;
        $advtext = "";
        next;
     }
  }
  $advtext .= $advline;
}
$advtextx{$advkey} = $advtext;

# do basic initialization from parameters, ini file and standard input

$rc = init($args_start);

$opt_log = $opt_workpath . $opt_log;
open FH, ">>$opt_log" or die "can't open $opt_log: $!";

logit(0,"EVENTAUDIT000I - ITM_Situation_Information $gVersion $args_start");

my $arg_start = join(" ",@ARGV);

$hdri++;$hdr[$hdri]="Situation Status History Audit Report $gVersion";
$hdri++;$hdr[$hdri] = "Runtime parameters: $args_start";

# process two sources of situation event status data
# much of the setup work is performed there

$rc = init_all();

# there are cases where event history records are months or years old.
# to avoid unnecessary processing, limit the lookback view. Default is
# 7 days but can be specified differently including 0 meaning no limit.
if ($opt_days > 0) {
   my $limit_seconds = $opt_days*86400;
   if ($event_max > $event_min+$limit_seconds) {
      $event_min = $event_max - $limit_seconds;
   }
}
my $stamp_max = "1" . substr(sec2time($event_max),2,12) . "000";
my $stamp_min = "1" . substr(sec2time($event_min),2,12) . "000";

$event_dur = $event_max - $event_min;

# Now we need to do the event accounting postponed until we discovered
# the time range to be reported on - based on opt_days.

foreach my $f (sort { $a cmp $b } keys %nodex ) {  # First by Agent names or Managed System Names
   my $node_ref = $nodex{$f};
   print STDERR "working on loop 0 $f " .  __LINE__ . "\n" if $opt_v == 1;

   foreach my $g (sort { $a cmp $b } keys %{$node_ref->{situations}} ) { # second by situation name
      my $situation_ref = $node_ref->{situations}{$g};
      print STDERR "working on loop 0/situation $g " .  __LINE__ . "\n" if $opt_v == 1;

      foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{atoms}}) { # Next by atomize value - which might be null
         my $atomize_ref = $situation_ref->{atoms}{$h};
         print STDERR "working on loop 0/atomize [$h] " . __LINE__ . "\n" if $opt_v == 1;

          foreach my $t (sort {$a <=> $b  }   keys %{$atomize_ref->{tdetails}} ) { # by Agent Time/atomize
             my $tdetail_ref = $atomize_ref->{tdetails}{$t};
             if ($tdetail_ref->{tseconds} lt $stamp_min) {
                $atomize_ref->{postdelta} = $tdetail_ref->{deltastat};
                next;
             }
             print STDERR "working on loop 0/time [$t] " .  __LINE__ . "\n" if $opt_v == 1;
             $situation_ref->{count} += 1;
             $situation_ref->{open} += 1 if $tdetail_ref->{deltastat} eq "Y";
             $situation_ref->{close} += 1 if $tdetail_ref->{deltastat} eq "N";
             $situation_ref->{bad} += 1 if $tdetail_ref->{deltastat} eq "X";
             $situation_ref->{ack} += 1 if $tdetail_ref->{deltastat} eq "A";
             $situation_ref->{res} += 1 if $tdetail_ref->{deltastat} eq "F";
             $atomize_ref->{count} += 1;
             $atomize_ref->{open} += 1 if $tdetail_ref->{deltastat} eq "Y";
             $atomize_ref->{close} += 1 if $tdetail_ref->{deltastat} eq "N";
             $atomize_ref->{bad} += 1 if $tdetail_ref->{deltastat} eq "X";
             $atomize_ref->{ack} += 1 if $tdetail_ref->{deltastat} eq "A";
             $atomize_ref->{res} += 1 if $tdetail_ref->{deltastat} eq "F";
          }
      }
   }
}


my $outline;


# Analysis and summary of event information. Mostly the data is summarized and
# rolled into the situation_ref hashes.
foreach my $f (sort { $a cmp $b } keys %nodex ) {  # First by Agent names [Managed System Names]
   my $node_ref = $nodex{$f};
   print STDERR "working on loop 1 $f " .  __LINE__ . "\n" if $opt_v == 1;

   foreach my $g (sort { $a cmp $b } keys %{$node_ref->{situations}} ) { # second by situation name
      my $situation_ref = $node_ref->{situations}{$g};
      print STDERR "working on loop 1/situation $g " .  __LINE__ . "\n" if $opt_v == 1;
      my $sx = $sitx{$g};
      my $sitatomnull = 0;
      if (!defined $sx) {
         $advi++;$advonline[$advi] = "Situation Status on unknown situation $g on node $f";
         $advcode[$advi] = "EVENTAUDIT1001W";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = "TEMS";
         next;
      }

      foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{atoms}}) { # Next by atomize value - which might be null
         my $atomize_ref = $situation_ref->{atoms}{$h};
         print STDERR "working on loop 1/atomize [$h] " . __LINE__ . "\n" if $opt_v == 1;

          # Next by detail within atomize value. key is the global time stamp concatenated
          # with the input line number from the file to create a reliable ordering while
          # managing the possibility of duplicate global 999 stamps
          #
          # This is logically done twice, once for the agent point of view and second
          # by the TEMS point of view. We are particularly looking for evidence of
          # merged events which can be trouble.

          # Following walks through the agent side of the retrieval
          # With these we can figure out
          # DisplayItem set, but null values seen
          # DisplayItem set, but multiple identical atomize values seen
          # DisplayItem not set, but multiple results in same second

          my $hi = 0;
          foreach my $t (sort {$a <=> $b  }   keys %{$atomize_ref->{adetails}} ) { # by Agent Time/atomize
             my $adetail_ref = $atomize_ref->{adetails}{$t};
             $hi += 1;
             print STDERR "working on loop 1/time [$t] $hi " .  __LINE__ . "\n" if $opt_v == 1;
             next if $adetail_ref->{aseconds} lt $stamp_min;
             print STDERR "working on loop 1/time [$t] $hi " .  __LINE__ . "\n" if $opt_v == 1;
             my $asecs = $adetail_ref->{aseconds};               # agent side in whole seconds
             my $akey = $adetail_ref->{aseconds} . "|" . $h;
             my $asum_ref = $situation_ref->{asecs}{$akey};   # situation summary
             if (!defined $asum_ref) {
                my %asumref = (
                                    atom => $h,
                                    aseconds => $adetail_ref->{aseconds},
                                    results => 0,
                                    count => 0,
                                    debug => [],
                                    attrgct => 0,
                                    thrunode => $adetail_ref->{thrunode},
                                    table => $adetail_ref->{table},
                                 );
                $asum_ref = \%asumref;
                $situation_ref->{asecs}{$akey} = \%asumref;
                $asum_ref->{attrgct} = scalar keys %{$adetail_ref->{attrgs}};
             }
             if ($opt_debug == 1) {
                my @debugi = [__LINE__,$adetail_ref->{results},$h,$t,$adetail_ref->{l}];
                push @{$asum_ref->{debug}},\@debugi;
             }
             $asum_ref->{results} += $adetail_ref->{results};
             $asum_ref->{count} += 1;

             # record generated results as seen by agent
             # we can record number of results created by agent
             # and how many were "missed" because of DisplayItem conditions usually
             # or rarely duplicate agents. This is important because the agent
             # can often produce a lot of results and the TEMS only processes
             # a certain number per second.
             setbudget($g,$adetail_ref->{thrunode},$f,$adetail_ref->{table},$h);
             my $imiss = $adetail_ref->{results} - 1;
             $irowsize = $budget_situation_ref->{rowsize};
             $budget_total_ref->{results} += $adetail_ref->{results};
             $budget_total_ref->{nfwd_results} += $adetail_ref->{results} if $situation_ref->{tfwd} == 1;
             $budget_situation_ref->{results} += $adetail_ref->{results};
             $budget_situation_ref->{nfwd_results} += $adetail_ref->{results} if $situation_ref->{tfwd} == 1;
             $budget_thrunode_ref->{results} += $adetail_ref->{results};
             $budget_node_ref->{results} += $adetail_ref->{results};
             $budget_total_ref->{result_bytes} += $adetail_ref->{results} * $irowsize;
             $budget_total_ref->{nfwd_result_bytes} += $adetail_ref->{results} * $irowsize if $situation_ref->{tfwd} == 1;
             $budget_situation_ref->{result_bytes} += $adetail_ref->{results} * $irowsize;
             $budget_situation_ref->{nfwd_result_bytes} += $adetail_ref->{results} * $irowsize if $situation_ref->{tfwd} == 1;
             $budget_thrunode_ref->{result_bytes} += $adetail_ref->{results} * $irowsize;
             $budget_node_ref->{result_bytes} += $adetail_ref->{results} * $irowsize;
             $budget_situation_ref->{nodes}{$f} += 1;
             if ( $imiss > 0) {
                $budget_total_ref->{miss} += $imiss;
                $budget_situation_ref->{miss} += $imiss;
                $budget_thrunode_ref->{miss} += $imiss;
                $budget_node_ref->{miss} += $imiss;
                $budget_total_ref->{miss_bytes} += $imiss * $irowsize;
                $budget_situation_ref->{miss_bytes} += $imiss * $irowsize;
                $budget_thrunode_ref->{miss_bytes} += $imiss * $irowsize;
                $budget_node_ref->{miss_bytes} += $imiss  * $irowsize;
             }
             $budget_situation_ref->{nodes}{$f} = 1;
          }

          # walk through the TEMS side of the retrieval
          $hi = 0;
          foreach my $t ( sort {$a <=> $b} keys %{$atomize_ref->{tdetails}}) {
             my $tdetail_ref = $atomize_ref->{tdetails}{$t};
             $hi += 1;
             if (defined $sitsx{$tdetail_ref->{thrunode}}{$g}) {
                print STDERR "working on loop 2 before start time/time $t $hi " .  __LINE__ . "\n" if $opt_v == 1;
                next if $tdetail_ref->{gbltmstmp} < $sitsx{$tdetail_ref->{thrunode}}{$g};
             }
             print STDERR "working on loop 2/time $t " .  __LINE__ .  " $hi $tdetail_ref->{tseconds} $stamp_min\n" if $opt_v == 1;
             next if $tdetail_ref->{tseconds} lt $stamp_min;
             print STDERR "working on loop 2/time $t " .  __LINE__ . "\n" if $opt_v == 1;
             my $tsecs = $tdetail_ref->{tseconds};
             my $tkey = $tdetail_ref->{tseconds} . "|" . $h;
             my $tsum_ref = $situation_ref->{tsecs}{$tkey};  # situation summary
             if (!defined $tsum_ref) {
                my %tsumref = (
                                    atom => $h,
                                    tseconds => $tdetail_ref->{tseconds},
                                    results => 0,
                                    count => 0,
                                    gbltmstmp => $tdetail_ref->{gbltmstmp},
                                    debug => [],
                                    attrgct => 0,
                                    thrunode => $tdetail_ref->{thrunode},
                                    table => $tdetail_ref->{table},
                                 );
                $tsum_ref = \%tsumref;
                $situation_ref->{tsecs}{$tkey} = \%tsumref;
                $tsum_ref->{attrgct} = scalar keys %{$tdetail_ref->{attrgs}};
             }
             $tsum_ref->{results} += $tdetail_ref->{results};
             $tsum_ref->{count} += 1;
             if ($opt_debug == 1) {
                my @debugi = [__LINE__,$tdetail_ref->{results},$h,$t,$tdetail_ref->{l}];
                push @{$tsum_ref->{debug}},\@debugi;
             }
          }

      }
      # finished walking through all the agent and tems side data
      print STDERR "finished loop " .  __LINE__ . "\n" if $opt_v == 1;

      # following logic scans summarized
      # observed atomize values in each second for agent/situation

      # first detection is for times recorded at the agent, the LCLTMSTMP value where
      # times associated with DisplayItem anomolies are easiest to detect.
      # Here are anomolies identified
      # DisplayItem set, but null values seen
      # DisplayItem set, but multiple identical atomize values seen
      # DisplayItem not set, but multiple results in same second


      foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{asecs}}) {
         my $asum_ref = $situation_ref->{asecs}{$h};
         setbudget($g,$asum_ref->{thrunode},$f,$asum_ref->{table},$asum_ref->{atom});
         # note the case where DisplayItem is set but null values seen
         if ($asum_ref->{atom} eq "") {
            if ($situation_ref->{atomize} ne "") {
               my $situation_dnull_ref = $situation_dnullx{$g};
               if (!defined $situation_dnull_ref) {
                  my %situation_dnullref = (
                                               reeval => $situation_ref->{reeval},
                                               instances => [],
                                            );
                  $situation_dnull_ref = \%situation_dnullref;
                  $situation_dnullx{$g} = \%situation_dnullref;
               }
               my @idnull = [$asum_ref->{aseconds},$asum_ref->{results},$f,$situation_ref->{atomize},$asum_ref->{atom}];
               push @{$situation_dnull_ref->{instances}},@idnull;
               $dnull_ct += 1;
            }
         }
         next if $asum_ref->{results} <= 1; # ignore single results
         # the results respresent a single attribute group. When a
         # situation formula is from a multi-row and a single row attribute group
         # the results will be bundled. Count is two but not a problem condition.
         if ($asum_ref->{attrgct} == 1) {
            $irowsize = 500;
            $newtabsizex{$asum_ref->{table}} += 1 if !defined $htabsize{$asum_ref->{table}};
            $irowsize = $htabsize{$asum_ref->{table}} if defined $htabsize{$asum_ref->{table}};
            if ($situation_ref->{atomize} eq "") {
               # budget calculation for null DisplayItem case
               $budget_total_ref->{null} += $asum_ref->{results};
               $budget_situation_ref->{null} += $asum_ref->{results};
               $budget_thrunode_ref->{null} += $asum_ref->{results};
               $budget_node_ref->{null} += $asum_ref->{results};
               $budget_total_ref->{null_bytes} += $asum_ref->{results} * $irowsize;
               $budget_situation_ref->{null_bytes} += $asum_ref->{results} * $irowsize;
               $budget_thrunode_ref->{null_bytes} += $asum_ref->{results} * $irowsize;
               $budget_node_ref->{null_bytes} += $asum_ref->{results} * $irowsize;
               my $situation_null_ref = $situation_nullx{$g};
               if (!defined $situation_null_ref) {
                  my %situation_nullref = (
                                             reeval => $situation_ref->{reeval},
                                             instances => [],
                                          );
                  $situation_null_ref = \%situation_nullref;
                  $situation_nullx{$g} = \%situation_nullref;
               }
               my @inull = [$asum_ref->{aseconds},$asum_ref->{results},$f,$situation_ref->{atomize},$asum_ref->{atom}];
               push @{$situation_null_ref->{instances}},@inull;
               $null_ct += 1;
            }
            if ($situation_ref->{atomize} ne "") {
               # budget calculation for dup DisplayItem case
               # This is the case where there were duplicates in DisplayItem for same seconds
               $budget_total_ref->{dup} += $asum_ref->{results};
               $budget_situation_ref->{dup} += $asum_ref->{results};
               $budget_thrunode_ref->{dup} += $asum_ref->{results};
               $budget_node_ref->{dup} += $asum_ref->{results};
               $budget_total_ref->{dup_bytes} += $asum_ref->{results} * $irowsize;
               $budget_situation_ref->{dup_bytes} += $asum_ref->{results} * $irowsize;
               $budget_thrunode_ref->{dup_bytes} += $asum_ref->{results} * $irowsize;
               $budget_node_ref->{dup_bytes} += $asum_ref->{results} * $irowsize;
               my $situation_dup_ref = $situation_dupx{$g};
               if (!defined $situation_dup_ref) {
                  my %situation_dupref = (
                                            reeval => $situation_ref->{reeval},
                                            instances => [],
                                         );
                  $situation_dup_ref = \%situation_dupref;
                  $situation_dupx{$g} = \%situation_dupref;
               }
               my @idup = [$asum_ref->{aseconds},$asum_ref->{results},$f,$situation_ref->{atomize},$asum_ref->{atom}];
               push @{$situation_dup_ref->{instances}},@idup;
               $dup_ct += 1;
            }
         }
      }

      # Now check for multiple events as recorded at TEMS in same second
      foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{tsecs}}) {
         my $tsum_ref = $situation_ref->{tsecs}{$h};
         next if $tsum_ref->{results} <= 1; # ignore single results
         setbudget($g,$tsum_ref->{thrunode},$f,$tsum_ref->{table},$tsum_ref->{atom});
         $irowsize = 500;
         $newtabsizex{$tsum_ref->{table}} += 1 if !defined $htabsize{$tsum_ref->{table}};
         $irowsize = $htabsize{$tsum_ref->{table}} if defined $htabsize{$tsum_ref->{table}};
         $budget_total_ref->{pure_merge} += $tsum_ref->{results};
         $budget_situation_ref->{pure_merge} += $tsum_ref->{results};
         $budget_thrunode_ref->{pure_merge} += $tsum_ref->{results};
         $budget_node_ref->{pure_merge} += $tsum_ref->{results};
         $budget_total_ref->{pure_merge_bytes} += $tsum_ref->{results} * $irowsize;
         $budget_situation_ref->{pure_merge_bytes} += $tsum_ref->{results} * $irowsize;
         $budget_thrunode_ref->{pure_merge_bytes} += $tsum_ref->{results} * $irowsize;
         $budget_node_ref->{pure_merge_bytes} += $tsum_ref->{results} * $irowsize;
         my $situation_merge_ref = $situation_mergex{$g};
         if (!defined $situation_merge_ref) {
            my %situation_mergeref = (
                                      reeval => $situation_ref->{reeval},
                                      instances => [],
                                   );
            $situation_merge_ref = \%situation_mergeref;
            $situation_mergex{$g} = \%situation_mergeref;
         }
         my @imerge = [$tsum_ref->{tseconds},$tsum_ref->{results},$f,$situation_ref->{atomize},$tsum_ref->{atom}];
         push @{$situation_merge_ref->{instances}},@imerge;
         $merge_ct += 1;
      }

      # start on sequence of details Y/N/A/F
      my $hi = 0;
      foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{atoms}}) {
         my $atomize_ref = $situation_ref->{atoms}{$h};
         $hi += 1;
         print STDERR "working on loop 3/time atom [$h] " .  __LINE__ .  " $hi\n" if $opt_v == 1;
         if ($h eq "") {
            print STDERR "working on loop 3/atom logic " .  __LINE__ .  " $hi\n" if $opt_v == 1;
            if ($situation_ref->{reeval} != 0) {
               print STDERR "working on loop 3/sampled sitation logic " .  __LINE__ .  " $hi\n" if $opt_v == 1;
               my $displayitem_prob = 1;
               my $displayitem_sec = "";
               my $tems_sec = 1;
               foreach my $t (keys %{$atomize_ref->{adetails}}) {
                  my $adetail_ref = $atomize_ref->{adetails}{$t};
                  next if $adetail_ref->{deltastat} ne "Y";
                  next if $adetail_ref->{results} <= 1;
                  # If there is a multi-row and a single attribute in the formula,
                  # both attributes will be returned. Do not complain about a duplicate
                  # result unless the attribute groups are the same.
                  my @aresult1 = split("[;]",$adetail_ref->{allresults}[0]);
                  $aresult1[1] =~ /(\S+)=(.*)/;
                  my $test1 = $1;
                  my @aresult2 = split("[;]",$adetail_ref->{allresults}[1]);
                  $aresult2[0] =~ /(\S+)=(.*)/;
                  my $test2 = $1;
                  if ($test1 eq $test2) {
                     $displayitem_prob = $adetail_ref->{results};
                     $displayitem_sec  = $t;
                  }
                  if ($displayitem_sec ne "") {
                     my $situation_miss_ref = $situation_missx{$g};
                     if (!defined $situation_miss_ref) {
                        my %situation_missref = (
                                                   reeval => $situation_ref->{reeval},
                                                   instances => [],
                                                );
                        $situation_miss_ref = \%situation_missref;
                        $situation_missx{$g} = \%situation_missref;
                     }
                     my @imiss = [$adetail_ref->{aseconds},$adetail_ref->{results},$f,$situation_ref->{atomize},$h];
                     push @{$situation_miss_ref->{instances}},@imiss;
                     $miss_ct += 1;
                  }
               }
               print STDERR "finished multi-row checking " .  __LINE__ .  " $hi\n" if $opt_v == 1;
            }
         }
         print STDERR "starting Y/N details " .  __LINE__ .  " $hi\n" if $opt_v == 1;
         # now run through the second by second TEMS details and track Y and N and A and F's
         my $detail_state = 1;   # always wait for initial Y record
         my $detail_start;
         my $detail_end;
         my $detail_lag = 0;
         my $detail_last = "";
         my $detail_results = 0;
         my $time_ref;
         my $time_thrunode_ref;
         my $time_node_ref;
         my $time_situation_ref;
         $hi = 0;
         foreach my $t (sort {$a cmp $b} keys %{$atomize_ref->{tdetails}}) {
            my $tdetail_ref = $atomize_ref->{tdetails}{$t};
            next if $tdetail_ref->{tseconds} lt $stamp_min;
            if ($atomize_ref->{postdelta} ne "") {
               if ($atomize_ref->{postdelta} eq "Y") {
                  if ($tdetail_ref->{deltastat} eq "N") {
                     $atomize_ref->{postdelta} = "";
                     $detail_start = $event_min;
                     $detail_results = 1;
                     $detail_state = 2;
                  }
               }
               $atomize_ref->{postdelta} = "";
            }
            $hi += 1;
            print STDERR "Starting loop 4 " .  __LINE__ .  " $hi\n" if $opt_v == 1;

            # prepare to capture the TEMS side workload on a second by second basis
            # the TEMS side timing can be spread out over many seconds and may not
            # reflect the initial agent result capture.
            setbudget($g,$tdetail_ref->{thrunode},$f,$tdetail_ref->{table},$h);
#            if ($budget_sitnodeatom_ref->{start} != 0) {
#            }
            $budget_sitnodeatom_ref->{start} = $tdetail_ref->{epoch} if $budget_sitnodeatom_ref->{start} == 0;
            $budget_sitnodeatom_ref->{start} = $tdetail_ref->{epoch} if $budget_sitnodeatom_ref->{start} > $tdetail_ref->{epoch};
            $budget_sitnodeatom_ref->{end} = $tdetail_ref->{epoch} if $budget_sitnodeatom_ref->{end} == 0;
            $budget_sitnodeatom_ref->{end} = $tdetail_ref->{epoch} if $budget_sitnodeatom_ref->{end} < $tdetail_ref->{epoch};
            $budget_sitnodeatom_ref->{reeval} = $situation_ref->{reeval};
            $budget_situation_ref->{bad} += 1 if $tdetail_ref->{deltastat} eq "X";
            $budget_situation_ref->{ack} += 1 if $tdetail_ref->{deltastat} eq "A";
            $budget_situation_ref->{res} += 1 if $tdetail_ref->{deltastat} eq "F";
            $irowsize = $budget_situation_ref->{rowsize};
            if ($situation_ref->{reeval} == 0) {                #pure situation
            print STDERR "Pure event loop 4 " .  __LINE__ .  " $hi\n" if $opt_v == 1;
               $atomize_ref->{pure_ct} += 1;
               $situation_ref->{pure_ct} += 1;
               my $ekey = substr($tdetail_ref->{lcltmstmp},0,11) . "00";
               setload($ekey,1,$tdetail_ref->{results},$tdetail_ref->{thrunode},$f,$g) if $opt_time == 1;
               $budget_total_ref->{event} += 1;
               $budget_situation_ref->{event} += 1;
               $budget_thrunode_ref->{event} += 1;
               $budget_node_ref->{event} += 1;
               $budget_total_ref->{open} += 1;
               $budget_situation_ref->{open} += 1;
               $budget_thrunode_ref->{open} += 1;
               $budget_node_ref->{open} += 1;
               $sitagt_ref->{event} += 1;
            } else {                                            # sampled situation
               print STDERR "Sampled event loop 4 [$t]" .  __LINE__ .  " $hi\n" if $opt_v == 1;
               # calculate open versus close for sampled events and thus calculate open time
               if ($detail_state == 1) {   # waiting for Y record
                  if ($tdetail_ref->{deltastat} eq "Y") {
                     $detail_start = $tdetail_ref->{epoch};
                     if ($detail_lag > 0) {
                        $budget_situation_ref->{yny_ct} += 1;
                        my $stime = $detail_start - $detail_lag;
                        my $sval = int(($stime+($situation_ref->{reeval}/2))/$situation_ref->{reeval});
                        my $sdiff = $stime - $sval*$situation_ref->{reeval};
                        $budget_situation_ref->{yny}{$sdiff} += 1 if abs($sdiff) > $opt_dgrace;
                     }
                     $detail_lag = $detail_start;
                     $detail_results = $tdetail_ref->{results};
                     $atomize_ref->{sampled_ct} += 1;
                     $situation_ref->{sampled_ct} += 1;
                     $situation_ref->{transitions} += 1;
                     setbudget($g,$tdetail_ref->{thrunode},$f,$tdetail_ref->{table},$h);
                     $budget_sitnodeatom_ref->{time_open} = $tdetail_ref->{epoch};
                     $budget_sitnodeatom_ref->{time_close} = 0;
                     $budget_sitnodeatom_ref->{last_stat} = $tdetail_ref->{deltastat};
                     $budget_sitnodeatom_ref->{open} += 1;
                     $budget_total_ref->{event} += 1;
                     $budget_situation_ref->{event} += 1;
                     $budget_thrunode_ref->{event} += 1;
                     $budget_node_ref->{event} += 1;
                     $budget_total_ref->{open} += 1;
                     $budget_situation_ref->{open} += 1;
                     $budget_thrunode_ref->{open} += 1;
                     $budget_node_ref->{open} += 1;
                     $budget_total_ref->{transitions} += 1;
                     $budget_situation_ref->{transitions} += 1;
                     $budget_thrunode_ref->{transitions} += 1;
                     $budget_node_ref->{transitions} += 1;
                     my $itimediff = get_epoch($tdetail_ref->{tseconds}) - get_epoch($tdetail_ref->{aseconds});
                     $budget_node_ref->{difftimes}{$itimediff} += 1;
                     my @idiffdet = [$g,$h,$itimediff,$tdetail_ref->{gbltmstmp},$tdetail_ref->{l}];
                     push @{$budget_node_ref->{diffdet}},\@idiffdet;
                     $sitagt_ref->{event} += 1;
                     $detail_state = 2;
                  } elsif ($detail_last eq "N") {
                     $tdetail_ref->{nn} += 1;          # record N followed by N, keep waiting for Y
                     $atomize_ref->{nn} += 1;
                     $situation_ref->{nn} += 1;
                     $budget_total_ref->{nn} += 1;
                     $budget_situation_ref->{nn} += 1;
                     $budget_thrunode_ref->{nn} += 1;
                     $budget_node_ref->{nn} += 1;
                     $budget_situation_ref->{nnnodes}{$f} = 1;
                  }
               } elsif ($detail_state == 2) {    # Y waiting for N or A record
                  if (($tdetail_ref->{deltastat} eq "N") or ($tdetail_ref->{deltastat} eq "A")) {
                     # result - do they stop flowing during Acknowledgement, or just ignored
                     $detail_end = $tdetail_ref->{epoch};
                     if ($detail_lag > 0) {
                        $budget_situation_ref->{yny_ct} += 1;
                        my $stime = $detail_end - $detail_lag;
                        my $sval = int(($stime+($situation_ref->{reeval}/2))/$situation_ref->{reeval});
                        my $sdiff = $stime - $sval*$situation_ref->{reeval};
                        $budget_situation_ref->{yny}{$sdiff} += 1 if abs($sdiff) > $opt_dgrace;
                     }
                     $budget_sitnodeatom_ref->{secs_open} += $detail_end - $budget_sitnodeatom_ref->{time_open};
                     $budget_sitnodeatom_ref->{time_close} = $tdetail_ref->{epoch};
                     $budget_sitnodeatom_ref->{close} += 1;
                     $budget_sitnodeatom_ref->{last_stat} = $tdetail_ref->{deltastat};
                     $tdetail_ref->{open_time} += $detail_end - $detail_start;
                     $atomize_ref->{open_time} += $detail_end - $detail_start;
                     $situation_ref->{open_time} += $detail_end - $detail_start;
                     $situation_ref->{transitions} += 1;
                     $budget_total_ref->{event} += 1;
                     $budget_situation_ref->{event} += 1;
                     $budget_thrunode_ref->{event} += 1;
                     $budget_node_ref->{event} += 1;
                     $budget_total_ref->{transitions} += 1;
                     $budget_situation_ref->{transitions} += 1;
                     $budget_thrunode_ref->{transitions} += 1;
                     $budget_node_ref->{transitions} += 1;

                     # estimate how many sampling intervals there were
                     my $evals = int(($detail_end - $detail_start)/$situation_ref->{reeval}) + 1;
                     for (my $e = 0; $e<=$evals;$e++) {
                        my $etime = $detail_start + $e*$situation_ref->{reeval};
                        my $ekey = "1" . substr(sec2time($etime),2,10) . "00";
                        setload($ekey,1,$detail_results,$tdetail_ref->{thrunode},$f,$g) if $opt_time == 1;
                     }
                     $budget_total_ref->{samp_confirm} += $evals;
                     $budget_situation_ref->{samp_confirm} += $evals;
                     $budget_thrunode_ref->{samp_confirm} += $evals;
                     $budget_node_ref->{samp_confirm} += $evals;
                     $budget_total_ref->{samp_confirm_bytes} += $evals * $irowsize;
                     $budget_situation_ref->{samp_confirm_bytes} += $evals * $irowsize;
                     $budget_thrunode_ref->{samp_confirm_bytes} += $evals * $irowsize;
                     $budget_node_ref->{samp_confirm_bytes} += $evals * $irowsize;
                     $budget_total_ref->{results} += $evals;
                     $budget_total_ref->{nfwd_results} += $evals if $situation_ref->{tfwd} == 1;
                     $budget_situation_ref->{results} += $evals;
                     $budget_situation_ref->{nfwd_results} += $evals if $situation_ref->{tfwd} == 1;
                     $budget_thrunode_ref->{results} += $evals;
                     $budget_node_ref->{results} += $evals;
                     $budget_total_ref->{result_bytes} += $evals * $irowsize;
                     $budget_total_ref->{nfwd_result_bytes} += $evals * $irowsize if $situation_ref->{tfwd} == 1;
                     $budget_situation_ref->{result_bytes} += $evals * $irowsize;
                     $budget_situation_ref->{nfwd_result_bytes} += $evals * $irowsize if $situation_ref->{tfwd} == 1;
                     $budget_thrunode_ref->{result_bytes} += $evals * $irowsize;
                     $budget_node_ref->{result_bytes} += $evals * $irowsize;
                     if ($tdetail_ref->{deltastat} eq "N") {
                        $detail_state = 1;
                     } else { # deltastat A - Acknowledge
                        $situation_ref->{ya} += 1;
                        $budget_total_ref->{ack} += 1;
                        $budget_situation_ref->{ack} += 1;
                        $budget_thrunode_ref->{ack} += 1;
                        $budget_node_ref->{ack} += 1;
                        $budget_total_ref->{ya} += 1;
                        $budget_situation_ref->{ya} += 1;
                        $budget_thrunode_ref->{ya} += 1;
                        $budget_node_ref->{ya} += 1;
                        $ack_ct += 1;
                        $detail_state = 3;
                     }
                  } elsif ($detail_last eq "Y") {
                     $tdetail_ref->{yy} += 1;          # record Y followed by Y, keep waiting for N
                     $atomize_ref->{yy} += 1;
                     $situation_ref->{yy} += 1;
                     $budget_total_ref->{yy} += 1;
                     $budget_situation_ref->{yy} += 1;
                     $budget_thrunode_ref->{yy} += 1;
                     $budget_node_ref->{yy} += 1;
                     $budget_situation_ref->{yynodes}{$f} = 1;
                     $budget_sitnodeatom_ref->{yy} += 1;
                  }
               } elsif ($detail_state == 3) {    # A waiting for F or Y record
                  my $iacktime = $tdetail_ref->{epoch} - $detail_lag;
                  $detail_lag = $detail_end;
                  if ($tdetail_ref->{deltastat} eq "Y"){
                     $situation_ref->{fy} += 1;
                     $budget_total_ref->{fy} += 1;
                     $budget_situation_ref->{fy} += 1;
                     $budget_thrunode_ref->{fy} += 1;
                     $budget_node_ref->{fy} += 1;
                     $detail_state = 1;
                     redo;
                  }
                  if ($tdetail_ref->{deltastat} eq "F"){
                     $situation_ref->{af} += 1;
                     $budget_total_ref->{af} += 1;
                     $budget_total_ref->{res} += 1;
                     $budget_total_ref->{ack_time} += $iacktime;
                     $budget_situation_ref->{af} += 1;
                     $budget_situation_ref->{res} += 1;
                     $budget_situation_ref->{ack_time} += $iacktime;
                     $budget_thrunode_ref->{af} += 1;
                     $budget_thrunode_ref->{res} += 1;
                     $budget_thrunode_ref->{ack_time} += $iacktime;
                     $budget_node_ref->{af} += 1;
                     $budget_node_ref->{res} += 1;
                     $budget_node_ref->{ack_time} += $iacktime;
                     $budget_node_ref->{sits}{$g} += 1;
                     $detail_state = 4;
                  }
               } elsif ($detail_state == 4) {    # F waiting for A or N record
                  $detail_lag = $detail_end;
                  if ($tdetail_ref->{deltastat} eq "N"){
                     $situation_ref->{fn} += 1;
                     $budget_total_ref->{fn} += 1;
                     $budget_situation_ref->{fn} += 1;
                     $budget_thrunode_ref->{fn} += 1;
                     $budget_node_ref->{fn} += 1;
                     $detail_state = 2;
                     redo;
                  }
                  if ($tdetail_ref->{deltastat} eq "A"){
                     $situation_ref->{fa} += 1;
                     $budget_total_ref->{fa} += 1;
                     $budget_total_ref->{ack} += 1;
                     $budget_situation_ref->{fa} += 1;
                     $budget_situation_ref->{ack} += 1;
                     $budget_thrunode_ref->{ack} += 1;
                     $budget_thrunode_ref->{fa} += 1;
                     $budget_node_ref->{fa} += 1;
                     $budget_node_ref->{ack} += 1;
                     $detail_state = 3;
                  }
               }
               $detail_last = $tdetail_ref->{deltastat};
            }
            if ($situation_ref->{reeval} > 0) {
               if ($detail_last eq "Y") {
                  $atomize_ref->{open_time} += $event_max - $detail_start;
                  $situation_ref->{open_time} += $event_max - $detail_start;
                  $atomize_ref->{sampled_ct} = int($atomize_ref->{open_time}/$situation_ref->{reeval});
                  $situation_ref->{sampled_ct} = int($situation_ref->{open_time}/$situation_ref->{reeval});

                  # estimate how many sampling intervals there were
                  my $evals = int(($event_max - $detail_start)/$situation_ref->{reeval}) + 1;
                  $budget_total_ref->{samp_confirm} += $evals;
                  $budget_situation_ref->{samp_confirm} += $evals;
                  $budget_thrunode_ref->{samp_confirm} += $evals;
                  $budget_node_ref->{samp_confirm} += $evals;
                  $budget_total_ref->{samp_confirm_bytes} += $evals * $irowsize;
                  $budget_situation_ref->{samp_confirm_bytes} += $evals * $irowsize;
                  $budget_thrunode_ref->{samp_confirm_bytes} += $evals * $irowsize;
                  $budget_node_ref->{samp_confirm_bytes} += $evals * $irowsize;
                  $budget_total_ref->{results} += $evals;
                  $budget_total_ref->{nfwd_results} += $evals if $situation_ref->{tfwd} == 1;
                  $budget_situation_ref->{results} += $evals;
                  $budget_situation_ref->{nfwd_results} += $evals if $situation_ref->{tfwd} == 1;
                  $budget_thrunode_ref->{results} += $evals;
                  $budget_node_ref->{results} += $evals;
                  $budget_total_ref->{result_bytes} += $evals * $irowsize;
                  $budget_total_ref->{nfwd_result_bytes} += $evals * $irowsize if $situation_ref->{tfwd} == 1;
                  $budget_situation_ref->{result_bytes} += $evals * $irowsize;
                  $budget_situation_ref->{nfwd_result_bytes} += $evals * $irowsize if $situation_ref->{tfwd} == 1;
                  $budget_thrunode_ref->{result_bytes} += $evals * $irowsize;
                  $budget_node_ref->{result_bytes} += $evals * $irowsize;
                  for (my $e = 0; $e<=$evals;$e++) {
                     my $etime = $detail_start + $e*$situation_ref->{reeval};
                     my $ekey = "1" . substr(sec2time($etime),2,10) . "00";
                     setload($ekey,1,$detail_results,$tdetail_ref->{thrunode},$f,$g) if $opt_time == 1;
                  }
               }
            }
         }
      }
      if ($sitatomnull > 0) {
         if ($situation_ref->{atomize} ne "") {
            $advi++;$advonline[$advi] = "DisplayItem [$situation_ref->{atomize}] with null atomize values situation [$g] node [$f]";
            $advcode[$advi] = "EVENTAUDIT1009W";
            $advimpact[$advi] = $advcx{$advcode[$advi]};
            $advsit[$advi] = "TEMS";
            $advsitx{$g} = 1;
         }
      }
   }
}


print STDERR "finished loop 1" .  __LINE__ . "\n" if $opt_v == 1;

my %situationx;

# now summarize by situation instead of node
foreach my $f (sort { $a cmp $b } keys %nodex ) {
   my $node_ref = $nodex{$f};
   foreach my $g (sort { $a cmp $b } keys %{$node_ref->{situations}} ) {
      my $situation_ref = $node_ref->{situations}{$g};
      my $situationx_ref = $situationx{$g};
      if (!defined $situationx_ref) {
         my %situationxref = (
                                count => 0,
                                open => 0,
                                bad => 0,
                                ack => 0,
                                res => 0,
                                ack_time => 0,
                                sampled_ct => 0,
                                pure_ct => 0,
                                close => 0,
                                atomize => $situation_ref->{atomize},
                                atoms => {},
                                reeval => $situation_ref->{reeval},
                                transitions => 0,
                                trans_rate => 0,
                                tfwd => 0,
                                nodes => {},
                                nn => 0,
                                yy => 0,
                                yny_ct => 0,
                                yny => {},
                                af => 0,
                                fa => 0,
                                fn => 0,
                                ya => 0,
                                time999 => {},
                                time998 => {},
                                ct999 => 0,
                                ct998 => 0,
                                node999 => {},
                                node998 => {},
                                atomize => "",
                             );
          $situationx_ref = \%situationxref;
          $situationx{$g} = \%situationxref;
      }
      $situationx_ref->{count} += $situation_ref->{count};
      $situationx_ref->{open} += $situation_ref->{open};
      $situationx_ref->{close} += $situation_ref->{close};
      $situationx_ref->{bad} += $situation_ref->{bad};
      $situationx_ref->{ack} += $situation_ref->{ack};
      $situationx_ref->{res} += $situation_ref->{res};
      $situationx_ref->{ack_time} += $situation_ref->{ack_time};
      $situationx_ref->{sampled_ct} += $situation_ref->{sampled_ct};
      $situationx_ref->{pure_ct} += $situation_ref->{pure_ct};
      $situationx_ref->{nn} += $situation_ref->{nn};
      $situationx_ref->{yy} += $situation_ref->{yy};
      $situationx_ref->{af} += $situation_ref->{fa};
      $situationx_ref->{fa} += $situation_ref->{af};
      $situationx_ref->{fn} += $situation_ref->{fn};
      $situationx_ref->{ya} += $situation_ref->{ya};
      $situationx_ref->{transitions} += $situation_ref->{transitions};
      $situationx_ref->{tfwd} = $situation_ref->{tfwd};
      $situationx_ref->{atomize} = $situation_ref->{atomize};
      $situationx_ref->{nodes}{$f} += 1;
      foreach my $h (keys %{$situation_ref->{atoms}}) {
         $situationx_ref->{atoms}{$h} += 1;
      }
      foreach my $h (keys %{$situation_ref->{time999}}) {
         $situationx_ref->{time999}{$h} += 1;
         $situationx_ref->{ct999} += 1;
      }
      foreach my $h (keys %{$situation_ref->{time998}}) {
         $situationx_ref->{time998}{$h} += 1;
         $situationx_ref->{ct998} += 1;
      }
      foreach my $h (keys %{$situation_ref->{node999}}) {
         $situationx_ref->{node999}{$h} += 1;
      }
      foreach my $h (keys %{$situation_ref->{node998}}) {
         $situationx_ref->{node998}{$h} += 1;
      }
   }
}

my $cache_total = 0;
foreach my $f (keys %budget_sitnodeatomx) {
   $budget_sitnodeatom_ref = $budget_sitnodeatomx{$f};
   my $sx = $sitx{$budget_sitnodeatom_ref->{sit}};
   if (defined $sx) {
      next if $sit_reeval[$sx] == 0;
   }
   $budget_sitnodeatom_ref->{end} = $event_max if  $budget_sitnodeatom_ref->{end} == $budget_sitnodeatom_ref->{start};
   if ($budget_sitnodeatom_ref->{time_close} == 0) {    # open and no close
      $budget_sitnodeatom_ref->{time_close} = $event_max;
      $budget_situation_ref->{end} = $event_max;
      $budget_situation_ref->{secs_open} += $budget_sitnodeatom_ref->{time_close} - $budget_sitnodeatom_ref->{time_open}
   }
   $budget_sitnodeatom_ref->{elapsed} = $budget_sitnodeatom_ref->{end} - $budget_sitnodeatom_ref->{start};
   $cache_total += 1;
   my $snkey = $budget_sitnodeatom_ref->{sit} . "|" . $budget_sitnodeatom_ref->{node};
   $budget_sitnode_ref = $budget_sitnodex{$snkey};
   next if !defined defined $budget_sitnode_ref;
   $budget_sitnode_ref->{sit} = $budget_sitnodeatom_ref->{sit};
   $budget_sitnode_ref->{node} = $budget_sitnodeatom_ref->{node};
   $budget_sitnode_ref->{atoms}{$budget_sitnodeatom_ref->{atom}} = 1;
   $budget_sitnode_ref->{secs_open} += $budget_sitnodeatom_ref->{secs_open};
   $budget_sitnode_ref->{open} += $budget_sitnodeatom_ref->{open};
   $budget_sitnode_ref->{close} += $budget_sitnodeatom_ref->{close};
   $budget_sitnode_ref->{elapsed} += $budget_sitnodeatom_ref->{elapsed};
   $budget_sitnode_ref->{cache} += 1;
   my $skey = $budget_sitnodeatom_ref->{sit};
   $budget_sit_ref = $budget_sitx{$skey};
   next if !defined defined $budget_sit_ref;
   $budget_sit_ref->{nodes}{$budget_sitnodeatom_ref->{node}} = 1;
   $budget_sit_ref->{secs_open} += $budget_sitnodeatom_ref->{secs_open};
   $budget_sit_ref->{open} += $budget_sitnodeatom_ref->{open};
   $budget_sit_ref->{close} += $budget_sitnodeatom_ref->{close};
   $budget_sit_ref->{elapsed} += $budget_sitnodeatom_ref->{elapsed};
   $budget_sit_ref->{cache} += 1;
}

my $res_rate;
my $ppc;

my $total_delay_ct = 0;
my $total_delay_overmin_ct = 0;
my $total_delay_overmin_sum = 0;
my $total_delay_avg = 0;

foreach my $f (sort { $budget_nodex{$b}->{result_bytes} <=> $budget_nodex{$a}->{result_bytes}} keys %budget_nodex ) {
   my $node_ref = $budget_nodex{$f};
   my $delay_ct;
   my $delay_sum;
   my $delay_min;
   my $delay_max;
   my $delay_mode;
   my $det1 = 1;
   my %delaysx;
   foreach my $g (sort  {$node_ref->{difftimes}{$b} <=> $node_ref->{difftimes}{$a}} keys %{$node_ref->{difftimes}}) {
      $delaysx{$g} += 1;
      if ($det1 == 1) {
         $delay_max = $g;
         $delay_min = $g;
      }
      $det1 = 0;
      $delay_min = $g if $g < $delay_min;
      $delay_max = $g if $g > $delay_max;
      $delay_ct += $node_ref->{difftimes}{$g};
      $delay_sum += $g * $node_ref->{difftimes}{$g};
   }
   next if $det1 == 1;
   my $delay_ct_target = int($delay_ct/2);
   my $delay_ct_current = 0;
   foreach my $g (sort {$a <=> $b} keys %{$node_ref->{difftimes}}) {
      $delay_ct_current += $node_ref->{difftimes}{$g};
      next if $delay_ct_current < $delay_ct_target;
      $delay_mode = $g;
      last;
   }
   $node_ref->{diffmin} = $delay_min;
   my $res_pc = 0;
   $res_pc = $delay_sum / $delay_ct if $delay_ct > 0;
   $ppc = sprintf '%.0f', $res_pc;
   $node_ref->{pdiff} = "[" . $delay_ct . "/" .$delay_min . "/" . $delay_mode . "/" . $ppc . "/" . $delay_max . "]";
   $total_delay_ct += $delay_ct;
   foreach my $g (sort  {$node_ref->{difftimes}{$b} <=> $node_ref->{difftimes}{$a}} keys %{$node_ref->{difftimes}}) {
      next if $g <= $delay_min;
      $total_delay_overmin_ct += $node_ref->{difftimes}{$g};
      $total_delay_overmin_sum += $node_ref->{difftimes}{$g} * ($g - $delay_min);
   }
}



$rptkey = "EVENTREPORT000";$advrptx{$rptkey} = 1;         # record report key
$sumi++;$sline[$sumi]="$rptkey: Event/Result Summary Budget Report\n";

$sumi++;$sline[$sumi]="Duration: $event_dur Seconds\n";

$res_rate = 0;
$res_rate = ($budget_total_ref->{event}*60)/$event_dur if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
$sumi++;$sline[$sumi]="Total Open/Close Events: $budget_total_ref->{event} $ppc/min\n";

$res_rate = 0;
$res_rate = ($budget_total_ref->{results}*60)/$event_dur if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
$sumi++;$sline[$sumi]="Total Results: $budget_total_ref->{results} $ppc/min\n";
my $ppc_event_rate = $ppc;

$res_rate = 0;
$res_rate = ($budget_total_ref->{nfwd_results}*60)/$event_dur if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;

my $npc = 0;
my $nes_rate = 0;
$nes_rate = ($budget_total_ref->{nfwd_results}*100)/$budget_total_ref->{results} if $budget_total_ref->{results} > 0;$npc = sprintf '%.2f', $nes_rate;
$sumi++;$sline[$sumi]="Total Non-Forwarded Results: $budget_total_ref->{nfwd_results} $ppc/min [$npc%]\n";

$res_rate = 0;
$res_rate = ($budget_total_ref->{result_bytes}*60)/($event_dur*1024) if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
my $worry_rate = ($res_rate*100)/500;
my $wpc = sprintf '%.2f%%', $worry_rate;
$sumi++;$sline[$sumi]="Total Result Bytes: $budget_total_ref->{result_bytes} $ppc K/min Worry[$wpc]\n";

$npc = 0;
$nes_rate = ($budget_total_ref->{nfwd_result_bytes}*100)/$budget_total_ref->{result_bytes} if $budget_total_ref->{result_bytes} > 0;$npc = sprintf '%.2f', $nes_rate;
my $ppc_result_rate = $ppc;
my $ppc_worry_pc = $wpc;
$res_rate = 0;
$res_rate = ($budget_total_ref->{nfwd_result_bytes}*60)/($event_dur*1024) if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
$sumi++;$sline[$sumi]="Total Non-Forwarded Result Bytes: $budget_total_ref->{nfwd_result_bytes} $ppc/min [$npc%]\n";

if ($ppc_result_rate >= 500) {
   my $crit_line = "6,Estimated Incoming result rate $ppc_result_rate  worried $ppc_worry_pc";
   push @crits,$crit_line;
}

$res_rate = ($budget_total_ref->{samp_confirm}*60)/$event_dur if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
$sumi++;$sline[$sumi]="Sampled Results Confirm: $budget_total_ref->{samp_confirm} $ppc/min\n";

my $ppc_confirm_rate = $ppc;
$res_rate = ($budget_total_ref->{samp_confirm_bytes}*60)/($event_dur*1024) if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
my $pcrate = 0;
$pcrate = ($budget_total_ref->{samp_confirm_bytes}*100)/$budget_total_ref->{result_bytes} if $budget_total_ref->{result_bytes} > 0;my $prpc = sprintf '%.2f', $pcrate;
$sumi++;$sline[$sumi]="Sampled Results Confirm Bytes: $budget_total_ref->{samp_confirm_bytes} $ppc K/min, $prpc% of total results\n";

my $confirm_pc = $prpc;
$res_rate = 0;
$res_rate = ($budget_total_ref->{miss}*60)/$event_dur if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
$sumi++;$sline[$sumi]="Missing DisplayItem: $budget_total_ref->{miss} $ppc/min\n";

$res_rate = 0;
$res_rate = ($budget_total_ref->{dup}*60)/$event_dur if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
$sumi++;$sline[$sumi]="Duplicate DisplayItem: $budget_total_ref->{dup} $ppc/min\n";

$res_rate = 0;
$res_rate = ($budget_total_ref->{null_bytes}*60)/$event_dur if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
$sumi++;$sline[$sumi]="Null DisplayItem: $budget_total_ref->{null} $ppc/min\n";

$res_rate = 0;
$res_rate = ($budget_total_ref->{pure_merge}*60)/$event_dur if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
$sumi++;$sline[$sumi]="Pure Merged Results: $budget_total_ref->{pure_merge} $ppc/min\n";

$sumi++;$sline[$sumi]="Open/Open transitions: $budget_total_ref->{yy}\n";

$sumi++;$sline[$sumi]="Close/Close transitions: $budget_total_ref->{nn}\n";

$res_rate = 0;
$res_rate = ($total_delay_overmin_sum)/($total_delay_overmin_ct) if $total_delay_overmin_ct > 0;$ppc = sprintf '%.2f', $res_rate;
$sumi++;$sline[$sumi]="Delay Estimate opens[$total_delay_ct] over_minimum [$total_delay_overmin_ct] over_average [$ppc seconds]\n";

$total_delay_avg = $ppc;



# pass to calculate Transitions/Agent/Hour  rate
# goal is to identify situations with many transitions, indicate
# potentially inefficient and/or useless situations
my $res_pc;
foreach $g (keys %budget_situationx) {
   my $situation_ref = $budget_situationx{$g};
   if ($event_dur > 0) {
      $res_rate = ($budget_situation_ref->{transitions}*3600)/$event_dur;
      my $ct = scalar keys %{$situation_ref->{nodes}};
      $situation_ref->{trans_rate} = $res_rate/$ct if $ct > 0;
   }
}

if ($null_ct > 0) {
   $rptkey = "EVENTREPORT001";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Multiple results in one second but DisplayItem missing or null atoms found\n";
   $cnt++;$oline[$cnt]="Situation,Type,Agent_Second,Results,Agent,Atomize,Atom,\n";
   foreach my $f (sort { $a cmp $b } keys %situation_nullx ) {  # By situation name
      my $situation_null_ref = $situation_nullx{$f};
      $advsitx{$f} = 1;
      my $ptype = "Sampled";
      $ptype = "Pure" if $situation_null_ref->{reeval} == 0;
      foreach $g ( @{$situation_null_ref->{instances}}) {
         my $isec = @{$g}[0];
         my $iresults = @{$g}[1];
         my $inode = @{$g}[2];
         my $atomize = @{$g}[3];
         my $atom = @{$g}[4];
         $outline = $f . ",";
         $outline .= $ptype . ",";
         $outline .= $isec . ",";
         $outline .= $iresults . ",";
         $outline .= $inode . ",";
         $outline .= $atomize . ",";
         $outline .= $atom . ",";
         $cnt++;$oline[$cnt]="$outline\n";
      }
   }
   my $situation_ct = scalar keys %situation_nullx;
   $advi++;$advonline[$advi] = "Situations [$situation_ct] lost events because DisplayItem missing or null Atoms - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1010W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}

if ($dup_ct > 0) {
   $rptkey = "EVENTREPORT002";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Multiple results in one second and DisplayItem defined\n";
   $cnt++;$oline[$cnt]="Situation,Type,Agent_Second,Results,Agent,Atomize,Atom,\n";
   foreach my $f (sort { $a cmp $b } keys %situation_dupx ) {  # By situation name
      my $situation_dup_ref = $situation_dupx{$f};
      $advsitx{$f} = 1;
      my $ptype = "Sampled";
      $ptype = "Pure" if $situation_dup_ref->{reeval} == 0;
      foreach $g ( @{$situation_dup_ref->{instances}}) {
         my $isec = @{$g}[0];
         my $iresults = @{$g}[1];
         my $inode = @{$g}[2];
         my $atomize = @{$g}[3];
         my $atom = @{$g}[4];
         $outline = $f . ",";
         $outline .= $ptype . ",";
         $outline .= $isec . ",";
         $outline .= $iresults . ",";
         $outline .= $inode . ",";
         $outline .= $atomize . ",";
         $outline .= $atom . ",";
         $cnt++;$oline[$cnt]="$outline\n";
      }
   }
   my $situation_ct = scalar keys %situation_dupx;
   $advi++;$advonline[$advi] = "Situations [$situation_ct] lost events because DisplayItem has duplicate atoms - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1011W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}

if ($dnull_ct > 0) {
   $rptkey = "EVENTREPORT003";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Results at Agent with DisplayItem and null Atom\n";
   $cnt++;$oline[$cnt]="Situation,Type,Agent_Second,Results,Agent,Atomize,Atom,\n";
   foreach my $f (sort { $a cmp $b } keys %situation_dnullx ) {  # By situation name
      my $situation_dnull_ref = $situation_dnullx{$f};
      $advsitx{$f} = 1;
      my $ptype = "Sampled";
      $ptype = "Pure" if $situation_dnull_ref->{reeval} == 0;
      foreach $g ( @{$situation_dnull_ref->{instances}}) {
         my $isec = @{$g}[0];
         my $iresults = @{$g}[1];
         my $inode = @{$g}[2];
         my $atomize = @{$g}[3];
         my $atom = @{$g}[4];
         $outline = $f . ",";
         $outline .= $ptype . ",";
         $outline .= $isec . ",";
         $outline .= $iresults . ",";
         $outline .= $inode . ",";
         $outline .= $atomize . ",";
         $outline .= $atom . ",";
         $cnt++;$oline[$cnt]="$outline\n";
      }
   }
   my $situation_ct = scalar keys %situation_dnullx;
   $advi++;$advonline[$advi] = "Situations [$situation_ct] lost events because DisplayItem had Null atoms - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1009W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}

if ($merge_ct > 0) {
   $rptkey = "EVENTREPORT004";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Situations with Multiple results at TEMS with same DisplayItem at same second\n";
   $cnt++;$oline[$cnt]="Situation,Type,TEMS_Second,Results,Agent,Atomize,Atom,\n";
   foreach my $f (sort { $a cmp $b } keys %situation_mergex ) {  # By situation name
      my $situation_merge_ref = $situation_mergex{$f};
      $advsitx{$f} = 1;
      my $ptype = "Sampled";
      $ptype = "Pure" if $situation_merge_ref->{reeval} == 0;
      foreach $g ( @{$situation_merge_ref->{instances}}) {
         my $isec = @{$g}[0];
         my $iresults = @{$g}[1];
         my $inode = @{$g}[2];
         my $atomize = @{$g}[3];
         my $atom = @{$g}[4];
         $outline = $f . ",";
         $outline .= $ptype . ",";
         $outline .= $isec . ",";
         $outline .= $iresults . ",";
         $outline .= $inode . ",";
         $outline .= $atomize . ",";
         $outline .= $atom . ",";
         $cnt++;$oline[$cnt]="$outline\n";
      }
   }
   my $situation_ct = scalar keys %situation_mergex;
   $advi++;$advonline[$advi] = "Situations [$situation_ct] lost [merged] events Multiple Events with same DisplayItem at same TEMS second - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1013W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}

if ($miss_ct > 0) {
   $rptkey = "EVENTREPORT005";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Situations with Multiple results at Agent with same DisplayItem at same second\n";
   $cnt++;$oline[$cnt]="Situation,Type,Agent_Second,Results,Agent,Atomize,Atom,\n";
   foreach my $f (sort { $a cmp $b } keys %situation_missx ) {  # By situation name
      my $situation_miss_ref = $situation_missx{$f};
      $advsitx{$f} = 1;
      my $ptype = "Sampled";
      $ptype = "Pure" if $situation_miss_ref->{reeval} == 0;
      foreach $g ( @{$situation_miss_ref->{instances}}) {
         my $isec = @{$g}[0];
         my $iresults = @{$g}[1];
         my $inode = @{$g}[2];
         my $atomize = @{$g}[3];
         my $atom = @{$g}[4];
         $outline = $f . ",";
         $outline .= $ptype . ",";
         $outline .= $isec . ",";
         $outline .= $iresults . ",";
         $outline .= $inode . ",";
         $outline .= $atomize . ",";
         $outline .= $atom . ",";
         $cnt++;$oline[$cnt]="$outline\n";
      }
   }
   my $situation_ct = scalar keys %situation_missx;
   $advi++;$advonline[$advi] = "Situations [$situation_ct] with multiple results at agent with same DisplayItem at same second - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1009W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}

my %tooclosex;
my $tooclose_ct = 0;
foreach my $f (sort { $a cmp $b } keys %nodex ) {
   my $node_ref = $nodex{$f};
   foreach my $g (sort { $a cmp $b } keys %{$node_ref->{situations}} ) {
      my $situation_ref = $node_ref->{situations}{$g};
      my $sx = $sitx{$g};
      if (defined $sx) {
         if ($sit_reeval[$sx] > 0) {
            foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{atoms}}) {
               my $atomize_ref = $situation_ref->{atoms}{$h};
               foreach my $t (sort {$a <=> $b} keys %{$atomize_ref->{adetails}}) {
                  my $adetail_ref = $atomize_ref->{adetails}{$t};
                  my $tt_ct = scalar keys %{$adetail_ref->{astamps}};
                  next if $tt_ct <= 1;
                  foreach my $j (sort {$a cmp $b} keys %{$adetail_ref->{astamps}}) {
                     my $table_ref =  $adetail_ref->{astamps}{$j};
                     my $ts_ct = scalar keys %{$table_ref};
                     next if $ts_ct <= 1;
                     my $lagt = 0;
                     foreach my $l (sort {$a <=> $b} keys %{$table_ref}) {
                        if ($lagt == 0) {
                           $lagt = $l;
                           next;
                        }
                        if ((get_epoch($l) - get_epoch($lagt)) < $sit_reeval[$sx]) {
                           $tooclosex{$g} = 1;
                           $tooclose_ct += 1;
                        }
                     }
                  }
               }
            }
         }
      }
   }
}


if ($tooclose_ct > 0) {
   $rptkey = "EVENTREPORT006";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Timestamps too close together - possible duplicate agents\n";
   $cnt++;$oline[$cnt]="Node,Situation,Reval,Atomize,Atom,Timestamp_Prev,Timestamp_Current,Agent_Second,\n";
   foreach my $f (sort { $a cmp $b } keys %nodex ) {
      my $node_ref = $nodex{$f};
      foreach my $g (sort { $a cmp $b } keys %{$node_ref->{situations}} ) {
         my $situation_ref = $node_ref->{situations}{$g};
         my $sx = $sitx{$g};
         if (defined $sx) {
            if ($sit_reeval[$sx] > 0) {
               foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{atoms}}) {
                  my $atomize_ref = $situation_ref->{atoms}{$h};
                  foreach my $t (sort {$a <=> $b} keys %{$atomize_ref->{adetails}}) {
                     my $adetail_ref = $atomize_ref->{adetails}{$t};
                     my $tt_ct = scalar keys %{$adetail_ref->{astamps}};
                     next if $tt_ct <= 1;
                     foreach my $j (sort {$a cmp $b} keys %{$adetail_ref->{astamps}}) {
                        my $table_ref =  $adetail_ref->{astamps}{$j};
                        my $ts_ct = scalar keys %{$table_ref};
                        next if $ts_ct <= 1;
                        my $lagt = 0;
                        foreach my $l (sort {$a <=> $b} keys %{$table_ref}) {
                           if ($lagt == 0) {
                              $lagt = $l;
                              next;
                           }
                           if ((get_epoch($l) - get_epoch($lagt)) < $sit_reeval[$sx]) {
                              $outline = $f . ",";
                              $outline .= $g . ",";
                              $outline .= $sit_reeval[$sx] . ",";
                              $outline .= $sit_atomize[$sx] . ",";
                              $outline .= $h . ",";
                              $outline .= $lagt . ",";
                              $outline .= $l . ",";
                              $outline .= $adetail_ref->{lcltmstmp} . ",";
                              $cnt++;$oline[$cnt]="$outline\n";
                           }
                        }
                     }
                  }
               }
            }
         }
      }
   }
}

$tooclose_ct = scalar keys %tooclosex;
if ($tooclose_ct > 0) {
   my $situation_ct = scalar keys %situation_mergex;
   $advi++;$advonline[$advi] = "Sampled situations [$tooclose_ct] with events too close for sampling definition - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1012W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}

# need data from tdetail_ref
my @toomany;
my $toomanyi = -1;
my %toomanysit;
foreach my $f (sort { $a cmp $b } keys %nodex ) {
   my $node_ref = $nodex{$f};
   foreach my $g (sort { $a cmp $b } keys %{$node_ref->{situations}} ) {
      my $situation_ref = $node_ref->{situations}{$g};
      my $sx = $sitx{$g};
      if (defined $sx) {
         if ($sit_reeval[$sx] == 0) {
            foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{atoms}}) {
               my $atomize_ref = $situation_ref->{atoms}{$h};
               foreach my $t (sort {$a <=> $b} keys %{$atomize_ref->{tdetails}}) {
                  my $tdetail_ref = $atomize_ref->{tdetails}{$t};
                  my $tt_ct = scalar keys %{$tdetail_ref->{tstamps}};
                  next if $tt_ct < 1;
                  foreach my $j (sort {$a cmp $b} keys %{$tdetail_ref->{tstamps}}) {
                     my $table_ref =  $tdetail_ref->{tstamps}{$j};
                     my $ts_ct = scalar keys %{$table_ref};
                     next if $ts_ct <= 1;
                     $toomanyi += 1;
                     $outline = $g . ",";
                     $outline .= $f . ",";
                     $outline .= $tdetail_ref->{thrunode} . ",";
                     $outline .= $j . ",";
                     $outline .= $h . ",";
                     $outline .= $t . ",";
                     my $atime_ct = 0;
                     my $atimes = "";
                     foreach my $l (sort {$a <=> $b} keys %{$table_ref}) {
                        $atimes .= $l . '[' . %{$table_ref}{$l} . "] ";
                        $atime_ct += 1;
                     }
                     chop $atimes;
                     $outline .= $atime_ct . ",";
                     $outline .= $atimes . ",";
                     $toomany[$toomanyi] = $outline;
                     $toomanysit{$g} = 1;
                  }
               }
            }
         }
      }
   }
}

if ($toomanyi > -1) {
   $rptkey = "EVENTREPORT028";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Pure Situations with multiple TIMESTAMP attributes in same TEMS second\n";
   $cnt++;$oline[$cnt]="Situation,Node,Thrunode,Table,Atomize,TEMS_Time,Agent_Count,Agent_Times,\n";
   for (my $t = 0; $t <= $toomanyi; $t++) {
      $cnt++;$oline[$cnt]="$toomany[$t]\n";
   }
   my $pmany = scalar keys %toomanysit;
   $advi++;$advonline[$advi] = "Pure situations with results from multiple timestamps [$pmany] cases - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1016W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}



my %donesit;
$rptkey = "EVENTREPORT007";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$cnt++;$oline[$cnt]="$rptkey: Detailed Attribute differences on first two merged results\n";
$cnt++;$oline[$cnt]="Situation,Node,Agent_Time,Reeval,Results,Atom,Atomize,Attribute_Differences\n";
foreach my $f (sort { $a cmp $b } keys %nodex ) {
   my $node_ref = $nodex{$f};
   foreach my $g (sort { $a cmp $b } keys %{$node_ref->{situations}} ) {
      next if !defined $advsitx{$g};
      my $situation_ref = $node_ref->{situations}{$g};
      foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{atoms}}) {
      my $atomize_ref = $situation_ref->{atoms}{$h};
         foreach my $t (sort {$a <=> $b} keys %{$atomize_ref->{adetails}}) {
            my $adetail_ref = $atomize_ref->{adetails}{$t};
            next if $adetail_ref->{results} < 2;
            $donesit{$g} += 1;
            next if $donesit{$g} > 1;
            my %attr1;
            my @aresult1 = split("[;]",$adetail_ref->{allresults}[0]);
            foreach my $r (@aresult1) {
               $r =~ /(\S+)=(.*)/;
               my $iattr = $1;
               my $ivalue = $2;
               $attr1{$iattr} = $ivalue;
            }

            my %attr2;
            my @aresult2 = split("[;]",$adetail_ref->{allresults}[1]);
            foreach my $r (@aresult2) {
               $r =~ /(\S+)=(.*)/;
               my $iattr = $1;
               my $ivalue = $2;
               $attr2{$iattr} = $ivalue;
            }
            my $pdiff = "";
            foreach my $r ( sort {$a cmp $b} keys %attr1) {
               next if $r eq "*PREDICATE";
               next if !defined $attr2{$r};
               next if !defined $attr1{$r};
               next if $attr2{$r} eq $attr1{$r};
               $pdiff .= $r . " 1[" . $attr1{$r} . "] 2[" . $attr2{$r} . "],";
            }
            next if $pdiff eq "";
            $outline = $g . ",";
            $outline .= $f . ",";
            $outline .= $t . ",";
            $outline .= $situation_ref->{reeval} . ",";
            $outline .= $adetail_ref->{results} . ",";
            $outline .= $situation_ref->{atomize} . ",";
            $outline .= $h . ",";
            $outline .= $pdiff . ",";
            $cnt++;$oline[$cnt]="$outline\n";
         }
      }
   }
}




my %nfwdsitx;

my $yy_nn_ct = 0;
my $vol_ct = 0;

$rptkey = "EVENTREPORT011";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$cnt++;$oline[$cnt]="$rptkey: Event/Results Budget Situations Report by Result Bytes\n";
$cnt++;$oline[$cnt]="Situation,Table,Rowsize,Reeval,Event,Event%,Event/min,Results,ResultBytes,Result%,Miss,MissBytes,Dup,DupBytes,Null,NullBytes,SampConfirm,SampConfirmBytes,PureMerge,PureMergeBytes,transitions,nodes,PDT\n";
foreach my $g (sort { $budget_situationx{$b}->{result_bytes} <=> $budget_situationx{$a}->{result_bytes} ||
                      $a cmp $b
                    } keys %budget_situationx ) {
   next if $g eq "_total_";
   my $situation_ref = $budget_situationx{$g};
   $outline = $situation_ref->{psit} . ",";
   $outline .= $situation_ref->{table} . ",";
   $outline .= $situation_ref->{rowsize} . ",";
   $outline .= $situation_ref->{reeval} . ",";
   $outline .= $situation_ref->{event} . ",";
   $res_pc = 0;
   $res_pc = ($situation_ref->{event}*100)/$budget_total_ref->{event} if $budget_total_ref->{event} > 0;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $res_rate = 0;
   $res_rate = ($situation_ref->{event}*60)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   $outline .= $situation_ref->{results} . ",";
   $outline .= $situation_ref->{result_bytes} . ",";
   $res_pc = 0;
   $res_pc = ($situation_ref->{result_bytes}*100)/$budget_total_ref->{result_bytes} if $budget_total_ref->{result_bytes} > 0;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $outline .= $situation_ref->{miss} . ",";
   $outline .= $situation_ref->{miss_bytes} . ",";
   $outline .= $situation_ref->{dup} . ",";
   $outline .= $situation_ref->{dup_bytes} . ",";
   $outline .= $situation_ref->{null} . ",";
   $outline .= $situation_ref->{null_bytes} . ",";
   $outline .= $situation_ref->{samp_confirm} . ",";
   $outline .= $situation_ref->{samp_confirm_bytes} . ",";
   $outline .= $situation_ref->{pure_merge} . ",";
   $outline .= $situation_ref->{pure_merge_bytes} . ",";
   $outline .= $situation_ref->{transitions} . ",";
   my $situationx_ref = $situationx{$g};
   my $node_ct = scalar keys %{$situationx_ref->{nodes}};
   $outline .= $node_ct . ",";
   $outline .= $situation_ref->{pdt} . ",";
   $cnt++;$oline[$cnt]="$outline\n";

   my $duragent = $event_dur * $node_ct;
   $res_rate = ($situation_ref->{transitions}*3600)/($duragent) if $duragent > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $vol_ct += 1 if $res_rate >= 1;
   if ($situation_ref->{tfwd} == 0) {   # is this event not forwarded
      if ($sit_forwarded > 0) {          # are any events forwarded
         $nfwdsitx{$g} = 1 if substr($g,0,8) ne "UADVISOR";
      }
   }
   $yy_nn_ct += $situation_ref->{yy} + $situation_ref->{nn};
}

$rptkey = "EVENTREPORT032";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$cnt++;$oline[$cnt]="$rptkey: Event/Results Budget Situations Report by Events\n";
$cnt++;$oline[$cnt]="Situation,Table,Rowsize,Reeval,Event,Event%,Event/min,Results,ResultBytes,Result%,Miss,MissBytes,Dup,DupBytes,Null,NullBytes,SampConfirm,SampConfirmBytes,PureMerge,PureMergeBytes,transitions,nodes,PDT\n";
foreach my $g (sort { $budget_situationx{$b}->{event} <=> $budget_situationx{$a}->{event} ||
                      $a cmp $b
                    } keys %budget_situationx ) {
   next if $g eq "_total_";
   my $situation_ref = $budget_situationx{$g};
   $outline = $situation_ref->{psit} . ",";
   $outline .= $situation_ref->{table} . ",";
   $outline .= $situation_ref->{rowsize} . ",";
   $outline .= $situation_ref->{reeval} . ",";
   $outline .= $situation_ref->{event} . ",";
   $res_pc = 0;
   $res_pc = ($situation_ref->{event}*100)/$budget_total_ref->{event} if $budget_total_ref->{event} > 0;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $res_rate = 0;
   $res_rate = ($situation_ref->{event}*60)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   $outline .= $situation_ref->{results} . ",";
   $outline .= $situation_ref->{result_bytes} . ",";
   $res_pc = 0;
   $res_pc = ($situation_ref->{result_bytes}*100)/$budget_total_ref->{result_bytes} if $budget_total_ref->{result_bytes} > 0;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $outline .= $situation_ref->{miss} . ",";
   $outline .= $situation_ref->{miss_bytes} . ",";
   $outline .= $situation_ref->{dup} . ",";
   $outline .= $situation_ref->{dup_bytes} . ",";
   $outline .= $situation_ref->{null} . ",";
   $outline .= $situation_ref->{null_bytes} . ",";
   $outline .= $situation_ref->{samp_confirm} . ",";
   $outline .= $situation_ref->{samp_confirm_bytes} . ",";
   $outline .= $situation_ref->{pure_merge} . ",";
   $outline .= $situation_ref->{pure_merge_bytes} . ",";
   $outline .= $situation_ref->{transitions} . ",";
   my $situationx_ref = $situationx{$g};
   my $node_ct = scalar keys %{$situationx_ref->{nodes}};
   $outline .= $node_ct . ",";
   $outline .= $situation_ref->{pdt} . ",";
   $cnt++;$oline[$cnt]="$outline\n";
}
$rptkey = "EVENTREPORT033";$advrptx{$rptkey} = 1;         # record report key
foreach my $f (keys %budget_sitx) {
   $budget_sit_ref = $budget_sitx{$f};
   $budget_sit_ref->{ofract} = $budget_sit_ref->{secs_open} / $budget_sit_ref->{elapsed} if  $budget_sit_ref->{elapsed} > 0;
   $budget_sit_ref->{cache_fract} = $budget_sit_ref->{cache} / $cache_total if  $budget_sit_ref->{elapsed} > 0;
}

foreach my $f (keys %budget_sitnodex) {
   $budget_sitnode_ref = $budget_sitnodex{$f};
   $budget_sitnode_ref->{cache_fract} = $budget_sitnode_ref->{cache} / $cache_total if  $budget_sitnode_ref->{elapsed} > 0;
}


my $cache_curr = 0;
$cnt++;$oline[$cnt]="\n";
$cnt++;$oline[$cnt]="$rptkey: Situations Open for long periods of time sorted by Cache Usage\n";
$cnt++;$oline[$cnt]="Situation,Open,Close,Cache,Cache_pc,Cache_cum,Open_secs,Elapsed,Open-pc,Nodes,Reeval,PDT\n";
foreach my $g (sort { $budget_sitx{$b}->{cache} <=> $budget_sitx{$a}->{cache} ||
                      $a cmp $b
                    } keys %budget_sitx ) {
   my $budget_sit_ref = $budget_sitx{$g};
   next if $budget_sit_ref->{open} < 2;
   my $sx = $sitx{$budget_sit_ref->{sit}};
   $outline = $budget_sit_ref->{sit} . ",";
   $outline .= $budget_sit_ref->{open} . ",";
   $outline .= $budget_sit_ref->{close} . ",";
   $outline .= $budget_sit_ref->{cache} . ",";
   $res_pc = 0;
   $res_pc = $budget_sit_ref->{cache_fract}*100;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $cache_curr += $budget_sit_ref->{cache};

   $res_pc = 0;
   $res_pc = ($cache_curr/$cache_total)*100;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";

   $outline .= $budget_sit_ref->{secs_open} . ",";
   $outline .= $budget_sit_ref->{elapsed} . ",";
   $res_pc = 0;
   $res_pc = $budget_sit_ref->{ofract}*100;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   my $nct = scalar keys %{$budget_sit_ref->{nodes}};
   $outline .= $nct . ",";
   $outline .= $sit_reeval[$sx] . "," if defined $sx;
   $outline .= $sit_pdt[$sx] . "," if defined $sx;
   $cnt++;$oline[$cnt]="$outline\n";
}

my $nfwdsit_ct = scalar keys %nfwdsitx;

if ( $nfwdsit_ct > 0) {
   $rptkey = "EVENTREPORT018";$advrptx{$rptkey} = 1;         # record report key
   $advi++;$advonline[$advi] = "Situations [$nfwdsit_ct] showing event statuses but event not forwarded - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1004W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";


   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Situations processed but not forwarded\n";
   $cnt++;$oline[$cnt]="Situation,Count,Nodes,\n";
   foreach my $g (sort { $budget_situationx{$b}->{result_bytes} <=> $budget_situationx{$a}->{result_bytes} ||
                         $a cmp $b
                       } keys %budget_situationx ) {
      next if $g eq "_total_";
      $advsitx{$g} = 1;
      my $situation_ref = $budget_situationx{$g};
      my $node_ct = scalar keys %{$situation_ref->{nodes}};
      if ($situation_ref->{tfwd} == 0) {   # is this event not forwarded
         if ($sit_forwarded > 0) {          # are any events forwarded
            if (substr($g,0,8) ne "UADVISOR") {
               $outline = $g . ",";
               $outline .= $situation_ref->{event} . ",";
               $outline .= $node_ct . ",";
               $cnt++;$oline[$cnt]="$outline\n";
            }
         }
      }
   }
}


$rptkey = "EVENTREPORT012";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$cnt++;$oline[$cnt]="$rptkey: Budget Report by Thrunode\n";
$cnt++;$oline[$cnt]="Thrunode,Event,Event%,Event/min,Results,ResultBytes,Result%,Miss,MissBytes,Dup,DupBytes,Null,NullBytes,SampConfirm,SampConfirmbytes,PureMerge,PureMergeBytes,transitions,\n";
foreach my $f (sort { $budget_thrunodex{$b}->{result_bytes} <=> $budget_thrunodex{$a}->{result_bytes} ||
                      $a cmp $b
                    } keys %budget_thrunodex ) {
   my $thrunode_ref = $budget_thrunodex{$f};
   $outline = $f . ",";
   $outline .= $thrunode_ref->{event} . ",";
   $res_pc = 0;
   $res_pc = ($thrunode_ref->{event}*100)/$budget_total_ref->{event} if $budget_total_ref->{event} > 0;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $res_rate = 0;
   $res_rate = ($thrunode_ref->{event}*60)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   $outline .= $thrunode_ref->{results} . ",";
   $outline .= $thrunode_ref->{result_bytes} . ",";
   $res_pc = 0;
   $res_pc = ($thrunode_ref->{result_bytes}*100)/$budget_total_ref->{result_bytes} if $budget_total_ref->{result_bytes} > 0;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $outline .= $thrunode_ref->{miss} . ",";
   $outline .= $thrunode_ref->{miss_bytes} . ",";
   $outline .= $thrunode_ref->{dup} . ",";
   $outline .= $thrunode_ref->{dup_bytes} . ",";
   $outline .= $thrunode_ref->{null} . ",";
   $outline .= $thrunode_ref->{null_bytes} . ",";
   $outline .= $thrunode_ref->{samp_confirm} . ",";
   $outline .= $thrunode_ref->{samp_confirm_bytes} . ",";
   $outline .= $thrunode_ref->{pure_merge} . ",";
   $outline .= $thrunode_ref->{pure_merge_bytes} . ",";
   $cnt++;$oline[$cnt]="$outline\n";
}



$rptkey = "EVENTREPORT013";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$cnt++;$oline[$cnt]="$rptkey: Budget Report by Node\n";
$cnt++;$oline[$cnt]="Node,Event,Results,ResultBytes,Result%,Miss,MissBytes,Dup,DupBytes,Null,NullBytes,SampConfirm,SampConfirmbytes,PureMerge,PureMergeBytes,transitions,delay[count/min/mode/avg/max],\n";
foreach my $f (sort { $budget_nodex{$b}->{result_bytes} <=> $budget_nodex{$a}->{result_bytes} ||
                      $a cmp $b
                    } keys %budget_nodex ) {
   my $node_ref = $budget_nodex{$f};
   $outline = $f . ",";
   $outline .= $node_ref->{event} . ",";
   $res_pc = 0;
   $res_pc = ($node_ref->{event}*100)/$budget_total_ref->{event} if $budget_total_ref->{event} > 0;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $res_rate = 0;
   $res_rate = ($node_ref->{event}*60)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   $outline .= $node_ref->{results} . ",";
   $outline .= $node_ref->{result_bytes} . ",";
   $res_pc = 0;
   $res_pc = ($node_ref->{result_bytes}*100)/$budget_total_ref->{result_bytes} if $budget_total_ref->{result_bytes} > 0;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $outline .= $node_ref->{miss} . ",";
   $outline .= $node_ref->{miss_bytes} . ",";
   $outline .= $node_ref->{dup} . ",";
   $outline .= $node_ref->{dup_bytes} . ",";
   $outline .= $node_ref->{null} . ",";
   $outline .= $node_ref->{null_bytes} . ",";
   $outline .= $node_ref->{samp_confirm} . ",";
   $outline .= $node_ref->{samp_confirm_bytes} . ",";
   $outline .= $node_ref->{pure_merge} . ",";
   $outline .= $node_ref->{pure_merge_bytes} . ",";
   $outline .= $node_ref->{transitions} . ",";
   $outline .= $node_ref->{pdiff} . ",";
   $cnt++;$oline[$cnt]="$outline\n";
}



$rptkey = "EVENTREPORT016";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$cnt++;$oline[$cnt]="$rptkey: Delay Report by Node and Situation\n";
$cnt++;$oline[$cnt]="Node,Situation,Atomize,Delay,Min_delay,GBLTMSTMP,Line,\n";
foreach my $f ( sort { $a cmp $b } keys %budget_nodex ) {
   my $budget_node_ref = $budget_nodex{$f};
   next if !defined $budget_node_ref->{diffmin};
   foreach my $d (@{$budget_node_ref->{diffdet}}) {
      my $isitname = $d->[0]->[0];
      my $iatomize = $d->[0]->[1];
      my $idiff = $d->[0]->[2];
      my $igbltmstmp = $d->[0]->[3];
      my $iline = $d->[0]->[4];
      next if $idiff <= $budget_node_ref->{diffmin} + 1;
      my $pdiff = $idiff - $budget_node_ref->{diffmin};
      $outline = $f . ",";
      $outline .= $isitname . ",";
      $outline .= $iatomize . ",";
      $outline .= $pdiff . ",";
      $outline .= $budget_node_ref->{diffmin} . ",";
      $outline .= $igbltmstmp . ",";
      $outline .= $iline . ",";
      $cnt++;$oline[$cnt]="$outline\n";
   }
}




my $node999_total = 0;
my $time999_total = 0;

$rptkey = "EVENTREPORT017";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$outline = "$rptkey: Extreme event arrival report SEQ999";
$cnt++;$oline[$cnt]="$outline\n";
$outline = "Situation,Count,Nodes,Times";
$cnt++;$oline[$cnt]="$outline\n";
foreach $g ( sort { $situationx{$b}->{ct999} <=> $situationx{$a}->{ct999}}  keys %situationx) {
   my $situation_ref = $situationx{$g};
   next if $situation_ref->{ct999} == 0;
   $outline = $g . ",";
   $outline .= $situation_ref->{ct999} . ",";
   my $ct = scalar keys %{$situation_ref->{node999}};
   $outline .= $ct . ",";
   $node999_total += $ct;
   my $tp = "";
   foreach my $t (sort {$situation_ref->{time999}{$b} <=> $situation_ref->{time999}{$a}} keys %{$situation_ref->{time999}}) {
      $tp .= $t . "[" . $situation_ref->{time999}{$t} . "] ";
      $time999_total += $situation_ref->{time999}{$t};
   }
   $outline .= $tp . ",";
   $cnt++;$oline[$cnt]="$outline\n";
}

if ($time999_total > 0) {
   $advi++;$advonline[$advi] = "Extreme Event Status agents[$node999_total] in $time999_total instances - See report $rptkey";
   $advcode[$advi] = "EVENTAUDIT1007W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}

$rptkey = "EVENTREPORT019";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$outline = "$rptkey: Segmented arrival report SEQ998";
$cnt++;$oline[$cnt]="$outline\n";
$outline = "Situation,Count,Nodes,Times,";
$cnt++;$oline[$cnt]="$outline\n";
foreach $g ( sort { $situationx{$b}->{ct998} <=> $situationx{$a}->{ct998}}  keys %situationx) {
   my $situation_ref = $situationx{$g};
   next if $situation_ref->{ct998} == 0;
   $outline = $g . ",";
   $outline .= $situation_ref->{ct998} . ",";
   my $ct = scalar keys %{$situation_ref->{node998}};
   $outline .= $ct . ",";
   my $tp = "";
   foreach my $t (sort {$situation_ref->{time998}{$b} <=> $situation_ref->{time998}{$a}} keys %{$situation_ref->{time998}}) {
      $tp .= $t . "[" . $situation_ref->{time998}{$t} . "] ";
   }
   $outline .= $tp . ",";
   $cnt++;$oline[$cnt]="$outline\n";
}

$rptkey = "EVENTREPORT020";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$outline = "$rptkey: Deltastat X (Problem) Report";
$cnt++;$oline[$cnt]="$outline\n";
$outline = "Situation,Count,";
$cnt++;$oline[$cnt]="$outline\n";
my $bad_ct = 0;
my $bad_total = 0;
foreach $g ( sort { $a cmp $b}  keys %budget_situationx) {
   my $budget_situation_ref = $budget_situationx{$g};
   next if $g eq "_total_";
   next if $budget_situation_ref->{bad} == 0;
   $bad_ct += 1;
   $bad_total +=  $budget_situation_ref->{bad};
   $outline = $g . ",";
   $outline .= $budget_situation_ref->{bad} . ",";
   $cnt++;$oline[$cnt]="$outline\n";
}

if ($bad_ct > 0) {
   $advi++;$advonline[$advi] = "Situations [$bad_ct] had lodge failures [$bad_total] - See report $rptkey";
   $advcode[$advi] = "EVENTAUDIT1008E";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}



if ($opt_time == 1) {

   $rptkey = "EVENTREPORT020";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Incoming workload sorted by time\n";
   $cnt++;$oline[$cnt]="Agent_Time,Count,Results,\n";
   foreach my $f (sort { $a <=> $b } keys %timex ) {
      my $time_ref = $timex{$f};
      $outline = $f . ",";
      $outline .= $time_ref->{count} . ",";
      $outline .= $time_ref->{results} . ",";
      $cnt++;$oline[$cnt]="$outline\n";
   }

   $rptkey = "EVENTREPORT021";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Incoming workload sorted by Time and Thrunode\n";
   $cnt++;$oline[$cnt]="Agent_Time,Thrunode,Count,Results,\n";
   foreach my $f (sort { $a <=> $b } keys %timex ) {
      my $time_ref = $timex{$f};
      foreach my $g  (sort { $a cmp $b } keys %{$time_ref->{by_thrunode}}) {
         my $time_thrunode_ref = $time_ref->{by_thrunode}{$g};
         $outline = $f . ",";
         $outline .= $g . ",";
         $outline .= $time_thrunode_ref->{count} . ",";
         $outline .= $time_thrunode_ref->{results} . ",";
         $cnt++;$oline[$cnt]="$outline\n";
      }
   }

   $rptkey = "EVENTREPORT022";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Incoming workload sorted by Time and Node\n";
   $cnt++;$oline[$cnt]="Agent_Time,Node,Count,Results,\n";
   foreach my $f (sort { $a <=> $b } keys %timex ) {
      my $time_ref = $timex{$f};
      foreach my $g  (sort { $a cmp $b } keys %{$time_ref->{by_node}}) {
         my $time_thrunode_ref = $time_ref->{by_node}{$g};
         $outline = $f . ",";
         $outline .= $g . ",";
         $outline .= $time_thrunode_ref->{count} . ",";
         $outline .= $time_thrunode_ref->{results} . ",";
         $cnt++;$oline[$cnt]="$outline\n";
      }
   }

   $rptkey = "EVENTREPORT023";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Incoming workload sorted by Time and Situation\n";
   $cnt++;$oline[$cnt]="Agent_Time,Node,Count,Results,\n";
   foreach my $f (sort { $a <=> $b } keys %timex ) {
      my $time_ref = $timex{$f};
      foreach my $g  (sort { $a cmp $b } keys %{$time_ref->{by_situation}}) {
         my $time_thrunode_ref = $time_ref->{by_situation}{$g};
         $outline = $f . ",";
         $outline .= $g . ",";
         $outline .= $time_thrunode_ref->{count} . ",";
         $outline .= $time_thrunode_ref->{results} . ",";
         $cnt++;$oline[$cnt]="$outline\n";
      }
   }

}


my $newtabsize_ct = scalar keys %newtabsizex;
if ($newtabsize_ct > 0) {
   $rptkey = "EVENTREPORT998";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: List of estimated table sizes\n";
   $cnt++;$oline[$cnt]="Table,Count,\n";
   foreach my $f (sort { $a cmp $b } keys %newtabsizex ) {
      $outline = $f . ",";
      $outline .= $newtabsizex{$f} . ",";
      $cnt++;$oline[$cnt]="$outline\n";
   }
}

my $missatom_ct = scalar keys %missatomx;
if ($missatom_ct > 0) {
   $rptkey = "EVENTREPORT024";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Situations using unknown DisplayItems\n";
   $cnt++;$oline[$cnt]="Situation,DisplayItem,\n";
   foreach my $f (sort { $a cmp $b } keys %missatomx ) {
      $outline = $f . ",";
      $outline .= $missatomx{$f} . ",";
      $cnt++;$oline[$cnt]="$outline\n";
   }
   $advi++;$advonline[$advi] = "Situations [$missatom_ct] had DisplayItem configured which was not in results - See report $rptkey";
   $advcode[$advi] = "EVENTAUDIT1014E";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}


if ($yy_nn_ct > 0) {
   my $yysit_ct = 0;
   my $nnsit_ct = 0;
   $rptkey = "EVENTREPORT025";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Situations showing Open->Open and Close->Close Statuses\n";
   $cnt++;$oline[$cnt]="Situation,Type,Count,Node_ct,Nodes,\n";

   foreach my $g (sort { $budget_situationx{$b}->{nn} <=> $budget_situationx{$a}->{nn} ||
                         $a cmp $b
                       } keys %budget_situationx ) {
      next if $g eq "_total_";
      my $situation_ref = $budget_situationx{$g};
      my $pnodes;
      my $pnode_ct;
      if ($situation_ref->{nn} > 0) {
         $nnsit_ct += 1;
         $outline = $g . ",";
         $outline .= "NN" . ",";
         $outline .= $situation_ref->{nn} . ",";
         $pnode_ct = scalar keys %{$situation_ref->{nnnodes}};
         $outline .= $pnode_ct . ",";
         $pnodes = "";
         foreach my $h (sort { $a cmp $b } keys %{$situation_ref->{nnnodes}}) {
            $pnodes .= $h . " ";
         }
         chop $pnodes;
         $outline .= $pnodes . ",";
         $cnt++;$oline[$cnt]="$outline\n";
         $advsitx{$g} = 1;
      }
      if ($situation_ref->{yy} > 0) {
         $yysit_ct += 1;
         $outline = $g . ",";
         $outline .= "YY" . ",";
         $outline .= $situation_ref->{yy} . ",";
         $pnode_ct = scalar keys %{$situation_ref->{yynodes}};
         $outline .= $pnode_ct . ",";
         $pnodes = "";
         foreach my $h (sort { $a cmp $b } keys %{$situation_ref->{yynodes}}) {
            $pnodes .= $h . " ";
         }
         chop $pnodes;
         $outline .= $pnodes . ",";
         $cnt++;$oline[$cnt]="$outline\n";
         $advsitx{$g} = 1;
      }
   }
   if ($yysit_ct > 0) {
      $advi++;$advonline[$advi] = "Situations [$yysit_ct] showing open->open transitions - see $rptkey";
      $advcode[$advi] = "EVENTAUDIT1005W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = "TEMS";
   }
   if ($nnsit_ct > 0) {
      $advi++;$advonline[$advi] = "Situations [$nnsit_ct] showing close->close transitions - see $rptkey";
      $advcode[$advi] = "EVENTAUDIT1006W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = "TEMS";
   }
}

if ($vol_ct > 0) {
   $rptkey = "EVENTREPORT026";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Situations showing high Open<->Close rate\n";
   $cnt++;$oline[$cnt]="Situation,Reeval,Rate,Node_ct,PDT\n";

   foreach my $g (sort {$a  cmp $b} keys %budget_situationx ) {
      next if $g eq "_total_";
      my $situation_ref = $budget_situationx{$g};
      my $node_ct = scalar keys %{$situation_ref->{nodes}};
      my $duragent = $event_dur * $node_ct;
      $res_rate = ($situation_ref->{transitions}*3600)/($duragent) if $duragent > 0;
      next if $res_rate < 1;
      $ppc = sprintf '%.2f', $res_rate;
      $outline = $g . ",";
      $outline .=  $situation_ref->{reeval} . ",";
      $outline .=  $ppc . ",";
      $outline .=  $node_ct . ",";
      $outline .=  $situation_ref->{pdt} . ",";
      $cnt++;$oline[$cnt]="$outline\n";
      $advsitx{$g} = 1;
   }
   $advi++;$advonline[$advi] = "Situations [$vol_ct] showing more than 1 open<->close transitions per hour per agent - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1003W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}

my $dyny_ct = 0;

foreach my $g (sort {$a  cmp $b} keys %budget_situationx ) {
   next if $g eq "_total_";
   my $situation_ref = $budget_situationx{$g};
   my $idiffs = scalar keys %{$situation_ref->{yny}};
   $dyny_ct += 1 if $idiffs > 0;
}

if ($dyny_ct > 0) {
   $rptkey = "EVENTREPORT027";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Sampled situations with iregular Open<->Close processing times\n";
   $cnt++;$oline[$cnt]="Situation,Reeval,YNY_Count,Non_Zero_diffs,\n";

   foreach my $g (sort {$a  cmp $b} keys %budget_situationx ) {
      next if $g eq "_total_";
      my $situation_ref = $budget_situationx{$g};
      my $idiffs = scalar keys %{$situation_ref->{yny}};
      next if $idiffs == 0;
      my $pdiff = "";
      foreach my $r ( sort {$a <=> $b} keys %{$situation_ref->{yny}}) {
         $pdiff .= $r . "[" . $situation_ref->{yny}{$r} . "] ";
      }
      chop $pdiff;
      $outline = $g . ",";
      $outline .=  $situation_ref->{reeval} . ",";
      $outline .=  $situation_ref->{yny_ct} . ",";
      $outline .=  $pdiff . ",";
      $cnt++;$oline[$cnt]="$outline\n";
      $advsitx{$g} = 1;
   }
   $advi++;$advonline[$advi] = "Situations [$dyny_ct] showing irregular open<->close transitions - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1015W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}

if ($ack_ct > 0) {
   $rptkey = "EVENTREPORT030";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Sampled situations with Acknowledge/Resurface Status\n";
   $cnt++;$oline[$cnt]="Situation,ACK_ct,RES_ct,ACK_Time,YA_ct,AF_ct,FA_ct,FN_ct\n";

   my $ack_sit = 0;
   foreach my $g (sort  {$budget_situationx{$b}->{ack_time} <=> $budget_situationx{$a}->{ack_time} ||
                         $a cmp $b} keys %budget_situationx) {
      next if $g eq "_total_";
      my $situation_ref = $budget_situationx{$g};
      next if $situation_ref->{ack} == 0;
      $ack_sit += 1;
      $outline = $g . ",";
      $outline .=  $situation_ref->{ack} . ",";
      $outline .=  $situation_ref->{res} . ",";
      $outline .=  $situation_ref->{ack_time} . ",";
      $outline .=  $situation_ref->{ya} . ",";
      $outline .=  $situation_ref->{af} . ",";
      $outline .=  $situation_ref->{fa} . ",";
      $outline .=  $situation_ref->{fn} . ",";
      $cnt++;$oline[$cnt]="$outline\n";
      $advsitx{$g} = 1;
   }
   $advi++;$advonline[$advi] = "Situations [$ack_sit] showing Acknowledge/Resurface status - see $rptkey";
   $advcode[$advi] = "EVENTAUDIT1017I";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";

   $rptkey = "EVENTREPORT031";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $cnt++;$oline[$cnt]="$rptkey: Nodes with situations with Acknowledge/Resurface Status\n";
   $cnt++;$oline[$cnt]="Node,ACK_ct,RES_ct,ACK_Time,YA_ct,AF_ct,FA_ct,FN_ct,Situations,\n";
   foreach my $f (sort  {$budget_nodex{$b}->{ack_time} <=> $budget_nodex{$a}->{ack_time} ||
                         $a cmp $b} keys %budget_nodex) {
      my $node_ref = $budget_nodex{$f};
      next if $node_ref->{ack_time} == 0;
      $ack_sit += 1;
      $outline = $f . ",";
      $outline .=  $node_ref->{ack} . ",";
      $outline .=  $node_ref->{res} . ",";
      $outline .=  $node_ref->{ack_time} . ",";
      $outline .=  $node_ref->{ya} . ",";
      $outline .=  $node_ref->{af} . ",";
      $outline .=  $node_ref->{fa} . ",";
      $outline .=  $node_ref->{fn} . ",";
      my $psits = "";
      foreach my $r ( sort {$a cmp $b} keys %{$node_ref->{sits}}) {
         $psits .= $r . "[" . $node_ref->{sits}{$r} . "] ";
      }
      chop $psits;
      $outline .=  $psits . ",";
      $cnt++;$oline[$cnt]="$outline\n";
   }
}

$rptkey = "EVENTREPORT029";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$cnt++;$oline[$cnt]="$rptkey: Event totals per Situation/Agent\n";
$cnt++;$oline[$cnt]="Situation,Node,Events,Rate/Min\n";
foreach my $g (sort {$sitagtx{$b}->{event} <=> $sitagtx{$a}->{event}} keys %sitagtx ) {
   $sitagt_ref = $sitagtx{$g};
   last if $sitagt_ref->{event} < 10;
   $outline = $sitagt_ref->{sitname} . ",";
   $outline .= $sitagt_ref->{node} . ",";
   $outline .= $sitagt_ref->{event} . ",";
   $res_rate = ($sitagt_ref->{event}*60)/$event_dur if $event_dur > 0;$ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   $cnt++;$oline[$cnt]="$outline\n";
}


$rptkey = "EVENTREPORT999";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
my $ititle = "Detailed report sorted by Node/Situation/Time - for situations recorded in Advisories";
$ititle = "Full report sorted by Node/Situation/Time" if $opt_allresults == 1;

$cnt++;$oline[$cnt]="$rptkey: $ititle\n";
$cnt++;$oline[$cnt]="Situation,Node,Thrunode,Agent_Time,TEMS_Time,Deltastat,Reeval,Results,Atomize,DisplayItem,LineNumber,PDT\n";
foreach my $f (sort { $a cmp $b } keys %nodex ) {
   my $node_ref = $nodex{$f};
   foreach my $g (sort { $a cmp $b } keys %{$node_ref->{situations}} ) {
      my $situation_ref = $node_ref->{situations}{$g};
      if ($opt_allresults == 0) {
         next if !defined $advsitx{$g};
      }
      my $sx = $sitx{$g};
      my $psitname = $g;
      if (defined $sx) {
         $psitname = $sit_fullname[$sx] if $sit_fullname[$sx] ne "";
      }
      foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{atoms}}) {
         my $atomize_ref = $situation_ref->{atoms}{$h};
         my $traceon = 0;
         my $loopct = 0;
        foreach my $t (sort {"" . $atomize_ref->{tdetails}{$a}->{gbltmstmp} cmp "" . $atomize_ref->{tdetails}{$b}->{gbltmstmp}} keys %{$atomize_ref->{tdetails}}) {
            my $tdetail_ref = $atomize_ref->{tdetails}{$t};
            $loopct += 1;
            $outline = $psitname . ",";
            $outline .= $f . ",";
            $outline .= $tdetail_ref->{thrunode} . ",";
            $outline .= $tdetail_ref->{lcltmstmp} . ",";
            $outline .= $tdetail_ref->{gbltmstmp} . ",";
            $outline .= $tdetail_ref->{deltastat} . ",";
            $outline .= $situation_ref->{reeval} . ",";
            $outline .= $tdetail_ref->{results} . ",";
            $outline .= $situation_ref->{atomize} . ",";
            $outline .= $h . ",";
            $outline .= $tdetail_ref->{l} . ",";
            $outline .= $sit_pdt[$sx] . "," if defined $sx;
            $cnt++;$oline[$cnt]="$outline\n";
            my @rarry = @{$tdetail_ref->{allresults}};
            my %pdtx;
            my $pdtseq = 0;
            my $pdtgrp;
            my @rrary;
            if (($#rarry > 0) or  ($opt_allresults == 1)){
               for (my $ri=0;$ri<= $#rarry;$ri++) {
                  my $rc = $ri + 1;
                  if (substr($rarry[$ri],0,1) eq "*") {
                     my $div_point = index($rarry[$ri],";");
                     my $pdt_atrs = substr($rarry[$ri],11,$div_point-11);
                     $pdt_atrs =~ /(\S+)\./;
                     $pdtgrp = $1;
                     for my $line (split / /,$pdt_atrs) {
                        next if substr($line,0,length($pdtgrp)) ne $pdtgrp;;
                        $pdtx{$line} = $pdtseq;
                        $pdtseq += 1
                     }
                     $outline = ",,,,,,,P,";
                     $outline .= substr($rarry[$ri],0,$div_point) . ",";
                     $cnt++;$oline[$cnt]="$outline\n";
                     $rarry[$ri] = substr($rarry[$ri],$div_point+1);
                  }
                  $outline = ",,,,,,," . $ri . ",";
                  @rrary = split /;/, $rarry[$ri];
                  foreach my $f (sort { $pdtx{$a} <=> $pdtx{$b}} keys %pdtx ) {
                     for my $frag (@rrary) {
                        next if substr($frag,0,length($f)) ne $f;
                        $outline .= $frag . ";";
                     }
                  }
                  $outline .= $rarry[$ri] . ",";
                  $cnt++;$oline[$cnt]="$outline\n";
               }
            }
         }
      }
   }
}


$opt_o = $opt_odir . $opt_o if index($opt_o,'/') == -1;

open OH, ">$opt_o" or die "unable to open $opt_o: $!";

if ($opt_nohdr == 0) {
   for (my $t=0; $t<=$hdri; $t++) {
      print OH $hdr[$t] . "\n";
   }
   print OH "\n";
}

for (my $t=0; $t<=$sumi; $t++) {
   print OH $sline[$t];
}
print OH "\n";

if ($advi != -1) {
   print OH "\n";
   print OH "Advisory Message Report - *NOTE* See advisory notes at report end\n";
   print OH "Impact,Advisory Code,Object,Advisory,\n";
   for (my $a=0; $a<=$advi; $a++) {
       my $mysit = $advsit[$a];
       my $myimpact = $advimpact[$a];
       my $mykey = $mysit . "|" . $a;
       $advx{$mykey} = $a;
   }
   foreach $f ( sort { $advimpact[$advx{$b}] <=> $advimpact[$advx{$a}] ||
                          $advcode[$advx{$a}] cmp $advcode[$advx{$b}] ||
                          $advsit[$advx{$a}] cmp $advsit[$advx{$b}] ||
                          $advonline[$advx{$a}] cmp $advonline[$advx{$b}]
                        } keys %advx ) {
      my $j = $advx{$f};
      next if $advimpact[$j] == -1;
      print OH "$advimpact[$j],$advcode[$j],$advsit[$j],$advonline[$j]\n";
      $max_impact = $advimpact[$j] if $advimpact[$j] > $max_impact;
      $advgotx{$advcode[$j]} = $advimpact[$j];
   }
} else {
   print OH "No Expert Advisory messages\n";
}
print OH "\n";

for (my $t = 0; $t<=$cnt; $t++) {
   print OH $oline[$t];
}

if ($advi != -1) {
   print OH "\n";
   print OH "Event History Advisory Messages, Meaning and Recovery suggestions follow\n\n";
   foreach $f ( sort { $a cmp $b } keys %advgotx ) {
      next if substr($f,0,10) ne "EVENTAUDIT";
      print OH "Advisory code: " . $f  . "\n";
      print OH "Impact:" . $advgotx{$f}  . "\n";
      print STDERR "$f missing\n" if !defined $advtextx{$f};
      print OH $advtextx{$f};
   }
}

my $rpti = scalar keys %advrptx;
if ($rpti != -1) {
   print OH "\n";
   print OH "Event History Reports - Meaning and Recovery suggestions follow\n\n";
   foreach $f ( sort { $a cmp $b } keys %advrptx ) {
      next if !defined $advrptx{$f};
      print STDERR "$f missing\n" if !defined $advtextx{$f};
      print OH "$f\n";
      print OH $advtextx{$f};
   }
}
close OH;

if ($opt_crit ne "") {
   if ($#crits != -1) {
      my $critfn = $opt_crit . $critical_fn;
      open(CRIT,">$critfn");
      for my $cline (@crits) {
         my $crit_line = $cline . "\n";
         print CRIT $crit_line;
      }
      close(CRIT);
   }
}




if ($opt_sum != 0) {
   my $sumline;
# EVENTAUD 100 25
   $sumline = "EVENTAUDIT ";
   my $padvi = $advi + 1;
   $sumline .= $max_impact . " ";
   $sumline .= $padvi . " ";
   $sumline .= $event_dur . " seconds ";
   $sumline .= $budget_total_ref->{event} . " events" . "[$ppc_event_rate/min] Confirm[$confirm_pc%] ";
   $sumline .= "results" . "[$ppc_result_rate" . "K/min] ";
   $sumline .= " worry" . "[$ppc_worry_pc] ";
   $sumline .= " delay[$total_delay_avg] ";
   $sumline .= " copy[$event_dur,$ppc_event_rate,$confirm_pc%,$ppc_result_rate" . "K,$ppc_worry_pc,$total_delay_avg] ";
   my $sumfn = $opt_odir . "eventaud.txt";
   open SUM, ">$sumfn" or die "Unable to open summary file $sumfn\n";
   print SUM "$sumline\n";
   close(SUM);
}

exit 0;

sub setload {
   my ($tkey,$icount,$inumres,$ithrunode,$inode,$isituation) = @_;
   my $time_ref = $timex{$tkey};
   if (!defined $time_ref) {
      my %timeref = (
                       count => 0,
                       results => 0,
                       by_thrunode => {},
                       by_node => {},
                       by_situation => {},
                    );
      $time_ref = \%timeref;
      $timex{$tkey} = \%timeref;
   }
   $time_ref->{count} += $icount;
   $time_ref->{results} += $inumres;

   my $time_thrunode_ref = $time_ref->{by_thrunode}{$ithrunode};
   if (!defined $time_thrunode_ref) {
      my %time_thrunoderef = (
                                count => 0,
                                results => 0,
                             );
      $time_thrunode_ref = \%time_thrunoderef;
      $time_ref->{by_thrunode}{$ithrunode}  = \%time_thrunoderef;
   }
   $time_thrunode_ref->{count} += $icount;
   $time_thrunode_ref->{results} += $inumres;

   my $time_node_ref = $time_ref->{by_node}{$inode};
   if (!defined $time_node_ref) {
      my %time_noderef = (
                            count => 0,
                            results => 0,
                         );
      $time_node_ref = \%time_noderef;
      $time_ref->{by_node}{$inode}  = \%time_noderef;
   }
   $time_node_ref->{count} += $icount;
   $time_node_ref->{results} += $inumres;

   my $time_situation_ref = $time_ref->{by_situation}{$isituation};
   if (!defined $time_situation_ref) {
      my %time_situationref = (
                                 count => 0,
                                 results => 0,
                              );
      $time_situation_ref = \%time_situationref;
      $time_ref->{by_situation}{$isituation}  = \%time_situationref;
   }
   $time_situation_ref->{count} += $icount;
   $time_situation_ref->{results} += $inumres;
}

# following logic sets up the collection buckets for the
# result budget data.
sub setbudget {
   my ($isitname,$ithrunode,$inode,$itable,$iatom) = @_;
   $budget_total_ref = $budget_situationx{$total_key};
   if (!defined $budget_total_ref) {
      my %budget_totalref = (
                               event => 0,
                               open => 0,
                               ack => 0,
                               res => 0,
                               results => 0,
                               result_bytes => 0,
                               miss => 0,
                               miss_bytes => 0,
                               dup => 0,
                               dup_bytes => 0,
                               null => 0,
                               null_bytes => 0,
                               pure_merge => 0,
                               pure_merge_bytes => 0,
                               samp_confirm => 0,
                               samp_confirm_bytes => 0,
                               transitions => 0,
                               trans_rate => 0,
                               nfwd_results => 0,
                               nfwd_result_bytes => 0,
                               yy => 0,
                               nn => 0,
                               ya => 0,
                               af => 0,
                               fa => 0,
                               fn => 0,
                               ya => 0,
                               ack_time => 0,
                            );
      $budget_total_ref = \%budget_totalref;
      $budget_situationx{$total_key} = \%budget_totalref;
   }

   $budget_situation_ref = $budget_situationx{$isitname};
   if (!defined $budget_situation_ref) {
      my %budget_situationref = (
                                   event => 0,
                                   open => 0,
                                   ack => 0,
                                   res => 0,
                                   results => 0,
                                   result_bytes => 0,
                                   miss => 0,
                                   miss_bytes => 0,
                                   dup => 0,
                                   dup_bytes => 0,
                                   null => 0,
                                   null_bytes => 0,
                                   pure_merge => 0,
                                   pure_merge_bytes => 0,
                                   samp_confirm => 0,
                                   samp_confirm_bytes => 0,
                                   table => "",
                                   rowsize => 500,
                                   reeval => 600,
                                   tfwd  => "",
                                   pdt => "",
                                   transitions => 0,
                                   trans_rate => 0,
                                   nfwd_results => 0,
                                   nfwd_result_bytes => 0,
                                   nodes => {},
                                   yy => 0,
                                   nn => 0,
                                   yynodes => {},
                                   nnnodes => {},
                                   yny_ct => 0,
                                   yny => {},
                                   bad => 0,
                                   psit => $isitname,
                                   ya => 0,
                                   af => 0,
                                   fa => 0,
                                   fn => 0,
                                   ya => 0,
                                   ack_time => 0,
                                );
      $budget_situation_ref = \%budget_situationref;
      $budget_situationx{$isitname} = \%budget_situationref;
   }
   my $sx = $sitx{$isitname};
   if (defined $sx) {
      $budget_situation_ref->{reeval} = $sit_reeval[$sx];
      $budget_situation_ref->{tfwd} = $sit_tfwd[$sx];
      $budget_situation_ref->{psit} = $sitfullx{$isitname} if defined $sitfullx{$isitname};
   }
   if (defined $itable) {
      if ($budget_situation_ref->{table} eq "") {
         $budget_situation_ref->{table} = $itable;
         $budget_situation_ref->{rowsize} = $htabsize{$itable} if defined $htabsize{$itable};
      }
   }

   $budget_thrunode_ref = $budget_thrunodex{$ithrunode};
   if (!defined $budget_thrunode_ref) {
      my %budget_thrunoderef = (
                                  event => 0,
                                  open => 0,
                                  ack => 0,
                                  res => 0,
                                  results => 0,
                                  result_bytes => 0,
                                  miss => 0,
                                  miss_bytes => 0,
                                  dup => 0,
                                  dup_bytes => 0,
                                  null => 0,
                                  null_bytes => 0,
                                  pure_merge => 0,
                                  pure_merge_bytes => 0,
                                  samp_confirm => 0,
                                  samp_confirm_bytes => 0,
                                  transitions => 0,
                                  trans_rate => 0,
                                  yy => 0,
                                  nn => 0,
                                  ya => 0,
                                  af => 0,
                                  fa => 0,
                                  fn => 0,
                                  ya => 0,
                                  ack_time => 0,
                            );
      $budget_thrunode_ref = \%budget_thrunoderef;
      $budget_thrunodex{$ithrunode} = \%budget_thrunoderef;
   }

   $budget_node_ref = $budget_nodex{$inode};
   if (!defined $budget_node_ref) {
      my %budget_noderef = (
                               event => 0,
                               open => 0,
                               ack => 0,
                               res => 0,
                               results => 0,
                               result_bytes => 0,
                               miss => 0,
                               miss_bytes => 0,
                               dup => 0,
                               dup_bytes => 0,
                               null => 0,
                               null_bytes => 0,
                               pure_merge => 0,
                               pure_merge_bytes => 0,
                               samp_confirm => 0,
                               samp_confirm_bytes => 0,
                               transitions => 0,
                               yy => 0,
                               nn => 0,
                               ya => 0,
                               af => 0,
                               fa => 0,
                               fn => 0,
                               ya => 0,
                               ack_time => 0,
                               af_time => 0,
                               trans_rate => 0,
                               difftimes => {},
                               diffdet => [],
                               pdiff => "",
                               diffmin => 0,
                               sits => {},
                            );
      $budget_node_ref = \%budget_noderef;
      $budget_nodex{$inode} = \%budget_noderef;
   }
   my $sakey = $isitname . "|" . $inode;
   $sitagt_ref = $sitagtx{$sakey};
   if (!defined $sitagt_ref) {
      my %sitagtref = (
                         sitname => $isitname,
                         node => $inode,
                         event => 0,
                      );
      $sitagt_ref = \%sitagtref;
      $sitagtx{$sakey} = \%sitagtref;
   }
   my $snakey = $isitname . "|" . $inode . "|" . $iatom;
   $budget_sitnodeatom_ref = $budget_sitnodeatomx{$snakey};
   if (!defined $budget_sitnodeatom_ref) {
      my %budget_sitnodeatomref = (
                                     sit => $isitname,
                                     node => $inode,
                                     atom => $iatom,
                                     reeval => 0,                                                    #
                                     last_stat => "",          # last status                         #
                                     time_open => 0,           # time situation event open at TEMS   #
                                     time_close => 0,          # time situation event closed at TEMS   #
                                     secs_open => 0,           # seconds open                        #
                                     open => 0,                # open count                          #
                                     close => 0,               # close count                         #
                                     start => 0,               # time first situation opened/closed  #
                                     end => 0,                 # time last situation opened/closed   #
                                     elapsed => 0,             # elapsed time
                                     yy => 0,                  # count open-open status cases        #
                                  );
      $budget_sitnodeatom_ref = \%budget_sitnodeatomref;
      $budget_sitnodeatomx{$snakey} = \%budget_sitnodeatomref;
   }
   my $snkey = $isitname . "|" . $inode;
   $budget_sitnode_ref = $budget_sitnodex{$snkey};
   if (!defined $budget_sitnode_ref) {
      my %budget_sitnoderef = (
                                 sit => "",
                                 node => "",
                                 atoms => {},
                                 secs_open => 0,           # time situation event open at TEMS
                                 open => 0,
                                 close => 0,
                                 elapsed => 0,             # sum of situation elapsed seconds
                                 cache => 0,
                                 cache_fract => 0,
                              );
      $budget_sitnode_ref = \%budget_sitnoderef;
      $budget_sitnodex{$snkey} = \%budget_sitnoderef;
   }
   my $skey = $isitname;
   $budget_sit_ref = $budget_sitx{$skey};
   if (!defined $budget_sit_ref) {
      my %budget_sitref = (
                             sit => $isitname,
                             nodes => {},
                             secs_open => 0,           # time situation event open at TEMS
                             open => 0,
                             close => 0,
                             elapsed => 0,
                             ofract => 0,
                             cache => 0,
                             cache_fract => 0,
                          );
      $budget_sit_ref = \%budget_sitref;
      $budget_sitx{$skey} = \%budget_sitref;
   }
}

sub newnam {
      my ($iid,$ifullname) = @_;
      $sitfullx{$iid} = $ifullname;
}
sub newsit {
      my ($isitname,$isitinfo,$ireev_days,$ireev_time,$ipdt) = @_;
      $isitinfo =~ s/\s+$//;   #trim trailing whitespace
      $siti += 1;
      $sit[$siti] = $isitname;
      $sitx{$isitname} = $siti;
      $sit_sitinfo[$siti] = $isitinfo;
      $sit_atomize[$siti] = "";
      $sit_fullname[$siti] = "";
      $sit_fullname[$siti] = $sitfullx{$isitname} if defined $sitfullx{$isitname};
      $sit_psit[$siti] = $isitname;
      $sit_psit[$siti] = $sit_fullname[$siti] if  $sit_fullname[$siti] ne "";
      $sit_pdt[$siti] = $ipdt;
      $sit_tfwd[$siti] = 0;
      $sit_tfwd[$siti] = 1 if index($isitinfo,"TFWD=Y") != -1;
      $sit_forwarded += $sit_tfwd[$siti];
      $sit_reeval[$siti] = 0;
      my $good_time = 1;
      if ((length($ireev_days) < 1) or (length($ireev_days) > 3) ) {
         $good_time = 0;
      }
      $good_time = 0 if length($ireev_time) > 6;
      if ($good_time == 1) {
         $ireev_days += 0;
         my $reev_time_hh = 0;
         my $reev_time_mm = 0;
         my $reev_time_ss = 0;
         if ($ireev_time ne "0") {
            $reev_time_hh = substr($ireev_time,0,2);
            $reev_time_mm = substr($ireev_time,2,2);
            $reev_time_ss = substr($ireev_time,4,2);
         }
         $sit_reeval[$siti] = $ireev_days*86400 + $reev_time_hh*3600 + $reev_time_mm*60 + $reev_time_ss;   # sampling interval in seconds
      }
      if (index($sit_sitinfo[$siti],"ATOM=") != -1) {
         $sit_sitinfo[$siti] =~ /ATOM=(.*?)[;~]/;
         if (defined $1) {
            $sit_atomize[$siti] = $1;
         } else {
            $sit_sitinfo[$siti] =~ /ATOM=(.*?)$/;
            $sit_atomize[$siti] = $1 if defined $1;
         }
      }
}
sub newstsh {
   my ($ill,$isitname,$ideltastat,$ioriginnode,$ilcltmstmp,$igbltmstmp,$inode,$iatomize,$iresults) = @_;
   # ignore some puzzling cases where on open event Y had a single tilda ~ or was null
   if ($ideltastat eq "Y") {
      return if ($iresults eq "~") or ($iresults eq "");
   }

   # MS_Offline type situations use fake ORIGINNODEs [managed systems] and thus do not relate to
   # normal situation events and so don't affect agent related situation processing.
#  $sx = $sitx{$isitname};
#  if (defined $sx) {
#     return if index($sit_pdt[$sx],"ManagedSystem.Status") != -1;
#  }

   # track when situation was last started
   if ($ideltastat eq "S") {
      $sitsx{$inode}{$isitname} = $igbltmstmp if !defined $sitsx{$inode}{$isitname};
      $sitsx{$inode}{$isitname} = $igbltmstmp if $igbltmstmp > $sitsx{$inode}{$isitname};
      return;
   }


   my $a_seconds = substr($ilcltmstmp,0,13) . "000";   # agent timestamp
   my $t_seconds = substr($igbltmstmp,0,13) . "000";   # tems  timestamp

   my $node_ref = $nodex{$ioriginnode};                # create a map by Agent name
   if (!defined $node_ref) {
      my %noderef = (
                       count => 0,
                       open => 0,
                       close => 0,
                       situations => {},
                       thrunodes => {},
                    );
      $node_ref = \%noderef;
      $nodex{$ioriginnode} = \%noderef;
   }
   $node_ref->{count} += 1;
   $node_ref->{open} += 1 if $ideltastat eq "Y";
   $budget_total_ref->{open} += 1 if $ideltastat eq "Y";
   $node_ref->{close} += 1 if $ideltastat eq "N";
   $node_ref->{thrunodes}{$inode} += 1;
   my $situation_ref = $node_ref->{situations}{$isitname};
   if (!defined $situation_ref) {
      my %situationref = (
                            count => 0,
                            open => 0,
                            close => 0,
                            bad => 0,
                            ack => 0,
                            ack_time => 0,
                            res => 0,
                            sampled_ct => 0,
                            pure_ct => 0,
                            open_time => 0,
                            atomize => "",
                            reeval => 0,
                            tfwd => 0,
                            transitions => 0,
                            nn => 0,
                            yy => 0,
                            af => 0,
                            fa => 0,
                            fn => 0,
                            ya => 0,
                            time999 => {},
                            time998 => {},
                            node999 => {},
                            node998 => {},
                            asecs => {},
                            tsecs => {},
                            atoms => {},
                         );
      $situation_ref = \%situationref;
      $node_ref->{situations}{$isitname} = \%situationref;
      my $sx = $sitx{$isitname};
      $situation_ref->{reeval} = $sit_reeval[$sx] if defined $sx;
      $situation_ref->{tfwd} = $sit_tfwd[$sx] if defined $sx;
      $situation_ref->{atomize} = $sit_atomize[$sx] if defined $sx;
   }
   # create a hash of last start time observed for this situation
   # we will ignore events recorded before that time at the TEMS.
   # counting is postponed so we can ignore ancient events
   my $atomize_ref = $situation_ref->{atoms}{$iatomize};
   if (!defined $atomize_ref) {
      my %atomizeref = (
                          count => 0,
                          open => 0,
                          close => 0,
                          bad => 0,
                          ack => 0,
                          res => 0,
                          open_time => 0,
                          reeval => 0,
                          sampled_ct => 0,
                          pure_ct => 0,
                          adetails => {},
                          tdetails => {},
                          asecs => {},
                          atime_min => "",
                          atime_max => "",
                          tsecs => {},
                          ttime_min => "",
                          ttime_max => "",
                          nn => 0,
                          yy => 0,
                          postdelta => "",
                       );
      $atomize_ref = \%atomizeref;
      $situation_ref->{atoms}{$iatomize} = \%atomizeref;
   }

   if ($atomize_ref->{atime_min} eq "") {
      $atomize_ref->{atime_min} = $a_seconds;
      $atomize_ref->{atime_max} = $a_seconds;
   }
   $atomize_ref->{atime_min} = $a_seconds if $a_seconds lt $atomize_ref->{atime_min};
   $atomize_ref->{atime_max} = $a_seconds if $a_seconds gt $atomize_ref->{atime_max};

   if ($atomize_ref->{ttime_min} eq "") {
      $atomize_ref->{ttime_min} = $t_seconds;
      $atomize_ref->{ttime_max} = $t_seconds;
   }
   $atomize_ref->{ttime_min} = $t_seconds if $t_seconds lt $atomize_ref->{ttime_min};
   $atomize_ref->{ttime_max} = $t_seconds if $t_seconds gt $atomize_ref->{ttime_max};

   # counting is postponed so we can ignore ancient events

   # first section captures activity on the Agent. Agents know nothing
   # about events going open/closed so only work with the open status records
   my $adetail_ref = ();
   if ($ideltastat eq "Y") {
      my $dkey = substr($ilcltmstmp,0,13) . "000";
      $adetail_ref = $atomize_ref->{adetails}{$dkey};
      if (!defined $adetail_ref) {
         my %adetailref = (
                            deltastat => $ideltastat,
                            gbltmstmp => $igbltmstmp,
                            lcltmstmp => $ilcltmstmp,
                            aseconds => $a_seconds,
                            tseconds => $t_seconds,
                            l => $ill,
                            rndx => 0,
                            results => 0,
                            eventh => 0,
                            attrgs => {},
                            table => "",
                            allresults => [],
                            pure_merge => 0,
                            pure_miss => 0,
                            pure_dup => 0,
                            pure_null => 0,
                            samp_confirm => 0,
                            samp_miss => 0,
                            samp_dup => 0,
                            samp_null => 0,
                            thrunode => $inode,
                            astamps => {},
                         );
         $adetail_ref = \%adetailref;
         $atomize_ref->{adetails}{$dkey} = \%adetailref;
      }
      $adetail_ref->{eventh} += 1 if substr($iresults,0,1) eq "*";
      my @segres = split("(?<!~)~(?!~)",$iresults); # split string by single ~ and not several ~ characters in a row
      $adetail_ref->{results} += $#segres;
      $adetail_ref->{results} += 1 if substr($segres[0],0,1) ne "*";
      # Collect all results for later usage
      foreach my $r (@segres) {
         push @{$adetail_ref->{allresults}},$r;
         # record the attribute group table name
         # needed to handle when multiples are present
         my $iattrg = "";
         my @tresult1 = split("[;]",$r);
         foreach my $s (@tresult1) {
            next if substr($s,0,1) eq "*";
            $s =~ /(\S+)\.(\S+)=(.*)/;
            $iattrg = $1 if defined $1;
            $adetail_ref->{attrgs}{$iattrg} = 1 if defined $iattrg;
            $adetail_ref->{table} = $iattrg if defined $iattrg;
            last;
         }
         my $ts = index($r,".TIMESTAMP=");
         if ($ts != 1) {
            my $pstring = substr($r,$ts);
            $pstring =~ /TIMESTAMP=(\d+)/;
            my $istamp = $1;
            $adetail_ref->{astamps}{$iattrg}{$istamp} += 1 if defined $istamp;
         }
         if ($situation_ref->{atomize} ne "") {
            $missatomx{$isitname} = $situation_ref->{atomize} if index($r,$situation_ref->{atomize}) == -1;
         }
      }
   }

   # second section captures activity at the TEMS, where Open and Close [Y/N] are determined
   if (($ideltastat eq "N")  or                                     # Handle event sitaution close
       ($ideltastat eq "X")  or                                     # Handle event sitaution problem
       ($ideltastat eq "A")  or                                     # Handle event sitaution Acknowledge
       ($ideltastat eq "F")  or                                     # Handle event sitaution Resurface
       ($ideltastat eq "Y")){                                       # Handle initial event situation open

      my $tkey = $t_seconds;
      my $tdetail_ref = $atomize_ref->{tdetails}{$tkey};
      if (!defined $tdetail_ref) {
         my %tdetailref = (
                             deltastat => $ideltastat,
                             gbltmstmp => $igbltmstmp,
                             lcltmstmp => $ilcltmstmp,
                             thrunode => $inode,
                             tseconds => $t_seconds,
                             aseconds => $a_seconds,
                             table => "",
                             epoch => 0,
                             l => $ill,
                             rndx => 0,
                             result1 => "",
                             result => [],
                             results => 0,
                             eventh => 0,
                             count => 0,
                             yy => 0,
                             nn => 0,
                             allresults => [],
                             allattrg => {},
                             pure_merge => 0,
                             pure_miss => 0,
                             pure_dup => 0,
                             pure_null => 0,
                             samp_confirm => 0,
                             samp_miss => 0,
                             samp_dup => 0,
                             samp_null => 0,
                             pure_merge => 0,
                             pure_miss => 0,
                             pure_dup => 0,
                             pure_null => 0,
                             samp_confirm => 0,
                             samp_miss => 0,
                             samp_dup => 0,
                             samp_null => 0,
                             thrunode => $inode,
                             debug => [],
                             tstamps => {},
                          );
         $tdetail_ref = \%tdetailref;
         $atomize_ref->{tdetails}{$tkey} = \%tdetailref;
      }
      if ($opt_debug == 1) {
         my @debugi = [__LINE__,$isitname,$ill,$inode];
         push @{$tdetail_ref->{debug}},\@debugi;
      }
      $tdetail_ref->{count} += 1;
      $tdetail_ref->{epoch} = get_epoch($igbltmstmp);
      $tdetail_ref->{result1} = substr($iresults,0,1);
      $tdetail_ref->{eventh} += 1 if $tdetail_ref->{result1} eq "*";
      my @segres = split("(?<!~)~(?!~)",$iresults); # split string by single ~ and not several ~ characters in a row
      $tdetail_ref->{results} += $#segres + 1;
      # In simple cases, there is just one result segment.
      # for cases with multiple result segments, capture the first two for comparison
      if ($ideltastat eq "Y") {
         if ($tdetail_ref->{rndx} < 2) {
            foreach my $r (@segres) {
               push @{$tdetail_ref->{result}},$r;
               $tdetail_ref->{rndx} += 1;
               last if $tdetail_ref->{rndx} > 1;
            }
         }
      }
      # Collect all results for later usage
      if ($ideltastat eq "Y") {
         foreach my $r (@segres) {
            push @{$tdetail_ref->{allresults}},$r;
            # record the attribute group table name
            # needed to handle when multiples are present
            my $iattrg = "";
            my @tresult1 = split("[;]",$r);
            foreach my $s (@tresult1) {
               next if substr($s,0,1) eq "*";
               $s =~ /(\S+)\.(\S+)=(.*)/;
               $iattrg = $1;
               $tdetail_ref->{attrgs}{$iattrg} = 1 if defined $iattrg;
               $tdetail_ref->{table} = $iattrg if defined $iattrg;
               last;
            }
            my $ts = index($r,".TIMESTAMP=");
            if ($ts != 1) {
               my $pstring = substr($r,$ts);
               $pstring =~ /TIMESTAMP=(\d+)/;
               my $istamp = $1;
               if (defined $iattrg) {
                  $tdetail_ref->{tstamps}{$iattrg}{$istamp} = 1 if defined $istamp;
               }
            }
         }
      }

      # track global start/stop time
      if ($event_min == 0) {
         $event_min = $tdetail_ref->{epoch};
         $event_max = $tdetail_ref->{epoch};
      }
      $event_min = $tdetail_ref->{epoch} if $tdetail_ref->{epoch} < $event_min;
      $event_max = $tdetail_ref->{epoch} if $tdetail_ref->{epoch} > $event_max;
   }
}

# There may be a better way to do this, but this was clear and worked.
# The input $lcount must be matched up to the number of columns
# SELECTED in the SQL.
# [1]  OGRP_59B815CE8A3F4403  OGRP_6F783DF5FF904988  2010  2010
sub parse_lst {
  my ($lcount,$inline) = @_;            # count of desired chunks and the input line
  my @retlist = ();                     # an array of strings to return
  my $chunk = "";                       # One chunk
  my $oct = 1;                          # output chunk count
  my $rest;                             # the rest of the line to process
  $inline =~ /\]\s*(.*)/;               # skip by [NNN]  field
  $rest = " " . $1 . "        ";
  my $lenrest = length($rest);          # length of $rest string
  my $restpos = 0;                      # postion studied in the $rest string
  my $nextpos = 0;                      # floating next position in $rest string

  # at each stage we can identify a field with values
  #         <blank>data<blank>
  # and a blank field
  #         <blank><blank>
  # We allow a single embedded blank as part of the field
  #         data<blank>data
  # for the last field, we allow imbedded blanks and logic not needed
  while ($restpos < $lenrest) {
     if ($oct < $lcount) {
        if (substr($rest,$restpos,2) eq "  ") {               # null string case
           $chunk = "";
           $oct += 1;
           push @retlist, $chunk;                 # record null data chunk
           $restpos += 2;
        } else {
           $nextpos = index($rest," ",$restpos+1);
           if (substr($rest,$nextpos,2) eq "  ") {
              $chunk .= substr($rest,$restpos+1,$nextpos-$restpos-1);
              push @retlist, $chunk;                 # record null data chunk
              $chunk = "";
              $oct += 1;
              $restpos = $nextpos + 1;
           } else {
              $chunk .= substr($rest,$restpos+1,$nextpos-$restpos);
              $restpos = $nextpos;
           }
        }
     } else {
        $chunk = substr($rest,$restpos+1);
        $chunk =~ s/\s+$//;                    # strip trailing blanks
        push @retlist, $chunk;                 # record last data chunk
        last;
     }
  }
  return @retlist;
}


# following routine gets data from txt or lst files. tems2sql.pl is an internal only program which can
# extract data from a TEMS database file. The way it is used here the results are a fixed column
# orientation.

sub init_all {
   my @knam_data;
   my $iid;
   my $ifullname;

   my @ksit_data;
   my $isitname;
   my $isitinfo;
   my $ireevdays;
   my $ireevtime;
   my $ipdt;

   my @kstsh_data;
   my $ideltastat;
   my $ioriginnode;
   my $ilcltmstmp;
   my $igbltmstmp;
   my $inode;
   my $iatomize;
   my $iresults;

   my $read_fn;

   # (1) the TNAME data
   if ($opt_txt == 1) {
      $read_fn = $opt_txt_tname;
      $read_fn = $opt_workpath . $opt_txt_tname if -e $opt_workpath . $opt_txt_tname;
   } else {
      $read_fn = $opt_lst_tname;
      $read_fn = $opt_workpath . $opt_lst_tname if -e $opt_workpath . $opt_lst_tname;
   }
   # perl \support\itm\bin\tems2sql.pl -txt -o -s ID -tc ID,FULLNAME  \support\itm\dat\kib.cat  QA1DNAME.DB

   # QA1DNAME would be missing on a remote TEMS capture
   if(open(KNAM, "< $read_fn")) {
      @knam_data = <KNAM>;
      close(KNAM);

      $ll = 0;
      foreach $oneline (@knam_data) {
         $ll += 1;
         if ($opt_txt == 1) {
            next if $ll < 5;
            chop $oneline;
            $oneline .= " " x 200;
            $iid = substr($oneline,0,32);
            $iid =~ s/\s+$//;   #trim trailing whitespace
            $ifullname = substr($oneline,33,256);
            $ifullname =~ s/\s+$//;   #trim trailing whitespace
         } else {
            next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
            ($iid,$ifullname) = parse_lst(2,$oneline);
            $iid =~ s/\s+$//;   #trim trailing whitespace
            $ifullname =~ s/\s+$//;   #trim trailing whitespace
         }
         newnam($iid,$ifullname);
      }
   }

   # (2) the TSITDESC data
   if ($opt_txt == 1) {
      $read_fn = $opt_txt_tsitdesc;
      $read_fn = $opt_workpath . $opt_txt_tsitdesc if -e $opt_workpath . $opt_txt_tsitdesc;
   } else {
      $read_fn = $opt_lst_tsitdesc;
      $read_fn = $opt_workpath . $opt_lst_tsitdesc if -e $opt_workpath . $opt_lst_tsitdesc;
   }
   # perl \support\itm\bin\tems2sql.pl -txt -o -tlim 0 -s SITNAME -tc SITNAME,SITINFO,REEV_DAYS,REEV_TIME,PDT \support\itm\dat\kib.cat  QA1CSITF.DB

   open(KSIT, "< $read_fn") || die("Could not open TSITDESC $read_fn\n");
   @ksit_data = <KSIT>;
   close(KSIT);

   $ll = 0;
   foreach $oneline (@ksit_data) {
      $ll += 1;
      if ($opt_txt == 1) {
         next if $ll < 5;
         chop $oneline;
         $oneline .= " " x 200;
         $isitname = substr($oneline,0,32);
         $isitname =~ s/\s+$//;   #trim trailing whitespace
         $isitinfo = substr($oneline,33,128);
         $ireevdays = substr($oneline,162,3);
         $ireevdays =~ s/\s+$//;   #trim trailing whitespace
         $ireevtime = substr($oneline,166,6);
         $ireevtime =~ s/\s+$//;   #trim trailing whitespace
         $ipdt = substr($oneline,175);
         $ipdt =~ s/\s+$//;   #trim trailing whitespace
      } else {
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         ($isitname,$isitinfo,$ireevdays,$ireevtime,$ipdt) = parse_lst(5,$oneline);
         $isitname =~ s/\s+$//;   #trim trailing whitespace
         $isitinfo =~ s/\s+$//;   #trim trailing whitespace
         $ireevdays =~ s/\s+$//;   #trim trailing whitespace
         $ireevtime =~ s/\s+$//;   #trim trailing whitespace
         $ipdt =~ s/\s+$//;   #trim trailing whitespace
      }
      newsit($isitname,$isitinfo,$ireevdays,$ireevtime,$ipdt);
   }

#  # (3) the TSITSTSH data
   if ($opt_txt == 1) {
      $read_fn = $opt_txt_tsitstsh;
      $read_fn = $opt_workpath . $opt_txt_tsitstsh if -e $opt_workpath . $opt_txt_tsitstsh;
   } else {
      $read_fn = $opt_lst_tsitstsh;
      $read_fn = $opt_workpath . $opt_lst_tsitstsh if -e $opt_workpath . $opt_lst_tsitstsh;
   }
   # perl \support\itm\bin\tems2sql.pl -txt -o -tr -s SITNAME -tlim 0 -tc SITNAME,DELTASTAT,ORIGINNODE,LCLTMSTMP,GBLTMSTMP,NODE,ATOMIZE,RESULTS \support\itm\dat\kib.cat  QA1CSTSH.DB

   open(KSTSH, "< $read_fn") || die("Could not open TSITSTSH $read_fn\n");
   @kstsh_data = <KSTSH>;
   close(KSTSH);

   $ll = 0;
   foreach $oneline (@kstsh_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $oneline .= " " x 200;
print STDERR "working on $ll\n" if $opt_v == 1;
      if ($opt_txt == 1) {
         $isitname = substr($oneline,0,32);
         $isitname =~ s/\s+$//;   #trim trailing whitespace
         $ideltastat = substr($oneline,33,1);
         $ideltastat =~ s/\s+$//;   #trim trailing whitespace
         $ioriginnode = substr($oneline,35,32);
         $ioriginnode =~ s/\s+$//;   #trim trailing whitespace
         $ilcltmstmp = substr($oneline,68,16);
         $ilcltmstmp =~ s/\s+$//;   #trim trailing whitespace
         $igbltmstmp = substr($oneline,85,16);
         $igbltmstmp =~ s/\s+$//;   #trim trailing whitespace
         $inode = substr($oneline,102,32);
         $inode =~ s/\s+$//;   #trim trailing whitespace
         $iatomize = substr($oneline,135,128);
         $iatomize =~ s/\s+$//;   #trim trailing whitespace
         $iresults = substr($oneline,264);
         $iresults =~ s/\s+$//;   #trim trailing whitespace
      } else {
         next if substr($oneline,0,1) ne "[";                    # Look for starting point
         ($isitname,$ideltastat,$ioriginnode,$ilcltmstmp,$igbltmstmp,$inode,$iatomize,$iresults) = parse_lst(8,$oneline);
         $isitname =~ s/\s+$//;   #trim trailing whitespace
         $ideltastat =~ s/\s+$//;   #trim trailing whitespace
         $ioriginnode =~ s/\s+$//;   #trim trailing whitespace
         $ilcltmstmp =~ s/\s+$//;   #trim trailing whitespace
         $igbltmstmp =~ s/\s+$//;   #trim trailing whitespace
         $inode =~ s/\s+$//;   #trim trailing whitespace
         $iatomize =~ s/\s+$//;   #trim trailing whitespace
         $iresults =~ s/\s+$//;   #trim trailing whitespace
      }
      next if ($ideltastat ne 'Y') and ($ideltastat ne 'N') and ($ideltastat ne 'X') and ($ideltastat ne 'A') and ($ideltastat ne 'F') and ($ideltastat ne 'S');

      # Squeeze out ending blanks in attribute results to report optics
      # And convert tabs, carriage returns, and linefeeds into symbolics
      # to avoid having reports display strangely by creating multiple lines.
      $iresults =~ s/[ ]*;/;/g;
      $iresults =~ s/[ ]*~/~/g;
      $iresults =~ s/\x09/\\t/g;
      $iresults =~ s/\x0A/\\n/g;
      $iresults =~ s/\x0D/\\r/g;
      newstsh($ll,$isitname,$ideltastat,$ioriginnode,$ilcltmstmp,$igbltmstmp,$inode,$iatomize,$iresults);
   }

}



# Get options from command line - first priority
sub init {
   while (@ARGV) {
      if ($ARGV[0] eq "-h") {
         &GiveHelp;                        # print help and exit
      }
      if ($ARGV[0] eq "-v") {
         $opt_v = 1;
         shift(@ARGV);
      } elsif ($ARGV[0] eq "-nohdr") {
         $opt_nohdr = 1;
         shift(@ARGV);
      } elsif ($ARGV[0] eq "-txt") {
         $opt_txt = 1;
         shift(@ARGV);
      } elsif ($ARGV[0] eq "-lst") {
         $opt_lst = 1;
         shift(@ARGV);
         if (defined $ARGV[0]) {
            if (substr($ARGV[0],0,1) ne "-") {
               $opt_lst_tems = shift(@ARGV);
            }
         }
      } elsif ($ARGV[0] eq "-allresults") {
         $opt_allresults = 1;
         shift(@ARGV);
      } elsif ($ARGV[0] eq "-time") {
         $opt_time = 1;
         shift(@ARGV);
      } elsif ($ARGV[0] eq "-sum") {
         $opt_sum = 1;
         shift(@ARGV);
      } elsif ($ARGV[0] eq "-debug") {
         $opt_debug = 1;
         shift(@ARGV);
      } elsif ($ARGV[0] eq "-debuglevel") {
         shift(@ARGV);
         $opt_debuglevel = shift(@ARGV);
         die "debuglevel specified but no level found\n" if !defined $opt_debuglevel;
         shift(@ARGV);
      } elsif ($ARGV[0] eq "-log") {
         shift(@ARGV);
         $opt_log = shift(@ARGV);
         die "log specified but no filename found\n" if !defined $opt_log;
         shift(@ARGV);
      } elsif ($ARGV[0] eq "-ini") {
         shift(@ARGV);
         $opt_ini = shift(@ARGV);
         die "ini specified but no filename found\n" if !defined $opt_ini;
         shift(@ARGV);
      } elsif ($ARGV[0] eq "-o") {
         shift(@ARGV);
         $opt_o = shift(@ARGV);
         die "-o output specified but no file found\n" if !defined $opt_o;
      } elsif ($ARGV[0] eq "-days") {
         shift(@ARGV);
         $opt_days = shift(@ARGV);
         die "-days but no number found\n" if !defined $opt_days;
      } elsif ($ARGV[0] eq "-dgrace") {
         shift(@ARGV);
         $opt_dgrace = shift(@ARGV);
         die "-dgrace but no number found\n" if !defined $opt_dgrace;
      } elsif ($ARGV[0] eq "-tsitstsh") {
         shift(@ARGV);
         $opt_tsitstsh = shift(@ARGV);
         die "-tsitstsh output specified but no file found\n" if !defined $opt_tsitstsh;
         die "-tsitstsh output specified file missing\n" if !-e $opt_tsitstsh;
      } elsif ($ARGV[0] eq "-odir") {
         shift(@ARGV);
         $opt_odir = shift(@ARGV);
         die "odir specified but no path found\n" if !defined $opt_odir;
      } elsif ($ARGV[0] eq "-workpath") {
         shift(@ARGV);
         $opt_workpath = shift(@ARGV);
         die "workpath specified but no path found\n" if !defined $opt_workpath;
      } elsif ( $ARGV[0] eq "-crit") {
         shift(@ARGV);
         $opt_crit = shift(@ARGV);
         die "option -crit with no following crit directory" if !defined $opt_crit;
      } else {
         $logfn = shift(@ARGV);
         die "log file not defined\n" if !defined $logfn;
      }
   }

   if (!defined $logfn) {$logfn = "";}
   if (!defined $opt_v) {$opt_v = 0;}
   if (!defined $opt_nohdr) {$opt_nohdr = 0;}
   if (!defined $opt_o) {$opt_o = "eventaud.csv";}
   if (!defined $opt_days) {$opt_days = 7;}
   if (!defined $opt_dgrace) {$opt_dgrace = 1;}
   if (!defined $opt_odir) {$opt_odir = "";}

   if (!defined $opt_workpath) {
      if ($gWin == 1) {
         $opt_workpath = $ENV{TEMP};
         $opt_workpath = "c:\temp" if !defined $opt_workpath;
      } else {
         $opt_workpath = $ENV{TMP};
         $opt_workpath = "/tmp" if !defined $opt_workpath;
      }
   }
   $opt_workpath =~ s/\\/\//g;    # switch to forward slashes, less confusing when programming both environments
   $opt_workpath .= '/';
   if ($opt_odir ne "") {
      $opt_odir =~ s/\\/\//g;    # switch to forward slashes, less confusing when programming both environments
      $opt_odir .= '/' if substr($opt_odir,-1,1) ne '/';
   }

   # Following are command line only defaults. All others can be set from the ini file

   if (!defined $opt_ini) {$opt_ini = "eventaud.ini";}         # default control file if not specified
   if (!defined $opt_debuglevel) {$opt_debuglevel=90;}         # debug logging level - low number means fewer messages
   if (!defined $opt_debug) {$opt_debug=0;}                    # debug - turn on rare error cases
   if (!defined $opt_allresults) {$opt_allresults=0;}               # initial testing show all results
   if (!defined $opt_time) {$opt_time=0;}               # initial testing show all results

   if (defined $opt_txt) {
      $opt_txt_tsitdesc = "QA1CSITF.DB.TXT";
      $opt_txt_tsitstsh = "QA1CSTSH.DB.TXT";
      $opt_txt_tsitstsh = $opt_tsitstsh if defined $opt_tsitstsh;
      $opt_txt_tname = "QA1DNAME.DB.TXT";
   }
   if (defined $opt_lst) {
      $opt_lst_tsitdesc = "HUB.TSITDESC.LST" if !defined $opt_lst_tsitdesc;
      $opt_lst_tname = "HUB.TNAME.LST" if !defined $opt_lst_tname;
      if (!defined $opt_lst_tsitstsh) {
         if ($opt_lst_tems eq "") {
            $opt_lst_tsitstsh = "HUB.TSITSTSH.LST";
         } else {
            $opt_lst_tsitstsh = $opt_lst_tems . ".TSITSTSH.LST";
         }
      }
   }


   # ini control file may be present

   if (-e $opt_ini) {                                      # make sure ini file is present

      open( FILE, "< $opt_ini" ) or die "Cannot open ini file $opt_ini : $!";
      my @ips = <FILE>;
      close FILE;

      # typical ini file scraping. Could be improved by validating parameters

      my $l = 0;
      foreach my $oneline (@ips)
      {
         $l++;
         chomp($oneline);
         next if (substr($oneline,0,1) eq "#");  # skip comment line
         @words = split(" ",$oneline);
         next if $#words == -1;                  # skip blank line
          if ($#words == 0) {                         # single word parameters
            if ($words[0] eq "verbose") {$opt_v = 1;}
            elsif ($words[0] eq "sum") {$opt_sum = 1;}
            else {
               print STDERR "EVENTAUDIT003E Control without needed parameters $words[0] - $opt_ini [$l]\n";
               $run_status++;
            }
            next;
         }
         my $uword = uc $words[0];
         if ($#words == 1) {
            # two word controls - option and value
            if ($words[0] eq "log") {$opt_log = $words[1];}
            elsif ($words[0] eq "o") {$opt_o = $words[1];}
            elsif ($words[0] eq "workpath") {$opt_workpath = $words[1];}
            elsif ($words[0] eq "lst_tsitdesc") {$opt_lst_tsitdesc = $words[1];}
            elsif ($words[0] eq "lst_tname") {$opt_lst_tname = $words[1];}
            elsif ($words[0] eq "lst_tsitstsh") {$opt_lst_tsitstsh = $words[1];$opt_lst_tems = "";}
            elsif (substr($uword,0,10) eq "EVENTAUDIT"){
               die "unknown advisory code $words[0]" if !defined $advcx{$uword};
               die "Advisory code $words[0] with no advisory impact" if !defined $words[1];
               $advcx{$uword} = $words[1];
            }
            else {
               print STDERR "EVENTAUDIT005E ini file $l - unknown control oneline\n"; # kill process after current phase
               $run_status++;
            }
            next;
         }
         if ($#words == 2) {
            next;
         }
         print STDERR "EVENTAUDIT005E ini file $l - unknown control $oneline\n"; # kill process after current phase
         $run_status++;
      }
   }

   # defaults for options not set otherwise

   if (!defined $opt_log) {$opt_log = "eventaud.log";}           # default log file if not specified
   if (!defined $opt_v) {$opt_v=0;}                            # verbose flag
   if (!defined $opt_o) {$opt_o="eventaud.csv";}               # default output file
   if (!defined $opt_workpath) {$opt_workpath="";}             # default is current directory
   if (!defined $opt_sum) {$opt_sum = 0;}                      # default no summary file
   if (!defined $opt_txt) {$opt_txt = 0;}                      # default no txt input
   if (!defined $opt_lst) {$opt_lst = 0;}                      # default no lst input

   $opt_workpath =~ s/\\/\//g;                                 # convert to standard perl forward slashes
   if ($opt_workpath ne "") {
      $opt_workpath .= "\/" if substr($opt_workpath,length($opt_workpath)-1,1) ne "\/";
   }


   # complain about options which must be present
   if (($opt_txt + $opt_lst) != 1) {
      print STDERR "EVENTAUDIT006E exactly one of txt/lst must be present\n";
      $run_status++;
   }

   # if any errors, then dump log and exit
   # this way we can show multiple errors at startup
   if ($run_status) { exit 1;}

}



#------------------------------------------------------------------------------
sub GiveHelp
{
  $0 =~ s|(.*)/([^/]*)|$2|;
  print <<"EndOFHelp";

  $0 v$gVersion

  This script surveys an ITM environment reporting in situation distributions

  Default values:
    log           : eventaud.log
    ini           : eventaud.ini
    debuglevel    : 90 [considerable number of messages]
    debug         : 0  when 1 some breakpoints are enabled]
    h             : 0  display help information
    v             : 0  display log messages on console
    vt            : 0  record http traffic on traffic.txt file
    lst           :    get data from KfwSQLClient SQL data
    txt           :    get data from TEMS2SQL data

  Example invovation
    $0  -lst

  Note: $0 uses an initialization file [default eventaud.ini] for some controls.

EndOFHelp
exit;
}


#------------------------------------------------------------------------------
# capture log record
sub logit
{
   my $level = shift;
   if ($level <= $opt_debuglevel) {
      my $iline = shift;
      my $itime = get_time();
      chop($itime);
      my $oline = $itime . " " . $level . " " . $iline;
      if ($opt_debuglevel >= 100) {
         my $ofile = (caller(0))[1];
         my $olino = (caller(0))[2];
         if (defined $ofile) {
            $oline = $ofile . ":" . $olino . " " . $oline;
         }
      }
      print FH "$oline\n";
      print "$oline\n" if $opt_v == 1;
   }
}

#------------------------------------------------------------------------------
# capture agent log record
#------------------------------------------------------------------------------
# capture agent error record

# write output log
sub datadumperlog
{
   require Data::Dumper;
   my $dd_msg = shift;
   my $dd_var = shift;
   print FH "$dd_msg\n";
   no strict;
   print FH Data::Dumper->Dumper($dd_var);
}

sub sec2time
{
   my ($itime) = @_;

   my $sec;
   my $min;
   my $hour;
   my $mday;
   my $mon;
   my $year;
   my $wday;
   my $yday;
   my $isdst;
   ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst)=gmtime($itime);
   return sprintf "%4d%02d%02d%02d%02d%02d",$year+1900,$mon+1,$mday,$hour,$min,$sec;
}

# return timestamp
sub get_time
{
   my $sec;
   my $min;
   my $hour;
   my $mday;
   my $mon;
   my $year;
   my $wday;
   my $yday;
   my $isdst;
   ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst)=localtime(time);
   return sprintf "%4d-%02d-%02d %02d:%02d:%02d\n",$year+1900,$mon+1,$mday,$hour,$min,$sec;
}
sub get_epoch {
   use POSIX;
   my $itm_stamp = shift;
   my $unixtime = $epochx{$itm_stamp};
   if (!defined $unixtime) {
     ( my $iyy, my $imo, my $idd, my $ihh, my $imm, my $iss ) =  unpack( "A2 A2 A2 A2 A2 A2", substr( $itm_stamp, 1 ) );
      my $wday = 0;
      my $yday = 0;
      $iyy += 100;
      $imo -= 1;
      $unixtime = timegm ($iss, $imm, $ihh, $idd, $imo, $iyy);
   }
   return $unixtime;
}

# get current time in ITM standard timestamp form
# History log

# 1.00000  : New script derived from sitcache.pl
# 1.01000  : Correct two display calculations
# 1.02000  : Corrections following AIX Analysis on Arrival testing
#          : Add SEQ 999 tracking, super fast arrival
#          : Add SEQ 998 tracking, multi-row arrivals
#          : Add Situation Predicate to reports 001 and 002
# 1.03000  : Handle -tlim 0 to TSITDESC to get full PDT
# 1.04000  : Advisory on null Atomize when DisplayItem is present
# 1.05000  : Advisories on DisplayItem present or absent issues.
# 1.06000  : Handle time references better in report, allow easy cross reference to same data.
# 1.07000  : rework logic to closer match more complex reality;
# 1.08000  : Correct Pure event counting logic, reduce 1005W impact to 10
#          : on 1010/1011/1012 - only emit advisory if multiple results on one attribute group
# 1.09000  : Split 1012 into 1012/1015 Pure/Sampled
#          : Ignore event history prior to most recent situation start per thrunode
#          : Update Report explanations
# 1.10000  : Add time based summary reports on incoming workload - needs -time option
#            Add report003 sorted in reverse by Transitions/Agent/Hour
# 1.11000  : Add Budget style reports
# 1.12000  : Limit result output unless advisories by default, add -addresults
#          : Add in long tail sampled confirm results
#          : Add in hash of table sizes
# 1.13000  : Add delay times to node report, and report global average
#          : Add TIMESTAMP related reports and resolve issues against regression set
# 1.14000  : Correct delay over minimum time logic
# 1.15000  : Enabled 1004W Advisory, added Non-Forward result count and bytes.
# 1.16000  : Rework logic so Summary report shows before Advisories
# 1.17000  : Detect cases where DisplayItem is not in proper form.
# 1.18000  : Don't tag unknown situations for detailed report section.
#          : Skip report006 if no too_close timestamps
#          : Add report025 for close-close and open-open transitions
# 1.19000  : Correct delay calculation
# 1.20000  : Correct delay mode calculation in node delay analysis
#            Add irregular event processing report and advisory
# 1.21000  : Correct report004 merged result report;
#            Add some new/corrected table sizes and report titles
# 1.22000  : correct/add some table sizes
# 1.23000  : correct/add some table sizes
#          : use TNAME to show fullname
# 1.24000  : Correct "Not Forwarded" logic
#            Correct/Add some table sizes
# 1.25000  : Correct "Not Forwarded" logic
#            Correct/Add some table sizes
#            Add detection of different timestamps in a single event
# 1.26000  : Add report on number of events
#          : And copy section to summary
# 1.27000  : Add critical report file
# 1.28000  : Report on Acknowledge/Resurface conditions, monitor MS_Offline type sits
# 1.29000  : Add/correct some table row sizes
# 1.30000  : Add/correct some table row sizes
#          : Add report032 by number of events
#          : Correct report031/2 by number of nodes
#          : Correct report999, sorting large numbers
# 1.31000  : Add/correct some table row sizes
#          : Handle allresults report when fullname is missing
#          : Handle some cases where there is little data
#          : Handle pure event results where there is no mini-predicate
# 1.32000  : Add/correct some table row sizes
#          : Add predicate related attributes at start in full report
# 1.33000  : Add/correct some table row sizes
# 1.34000  : Add/correct some table row sizes
# 1.35000  : Add report033 on estimated TSITSTSC cache usage and constant on situations
# 1.36000  : update some table sizes
# 1.37000  : update some table sizes
# 1.38000  : update some table sizes
# Following is the embedded "DATA" file used to explain
# advisories and reports.
__END__

EVENTAUDIT1001W
Text: Situation Status on unknown situation <situation> on node <agent>

Meaning: There are rare cases where situations run at an agent
even though the situation was deleted. This causes excessive work
at the least and confusion at the worst.

Recovery plan: If the TEMS and TEMA [Agent Support Library] are
at maintenance level ITM 630 FP2 or higher, recyle the agent
and the condition will be resolved. Otherwise contact IBM Support
for assistance.
--------------------------------------------------------------

EVENTAUDIT1003W
Text: Situation <situation> on showing <rate> open<->close transitions per hour over <count> agents

Meaning: A situation that shows a lot of transitions from open [Y]
to closed [N] and many times is not good situation. The best situations
show open and stay open until the condition is closed and then stay closed.

The impact is that the remote TEMS needs to create and transmit
situation events constantly. The condition also suggests that
whatever the condition is - no one is "fixing" it. Thus ITM
is consuming excess resources for no benefit.

Recovery plan: Here are three possible changes:
1) stop the situation, it has no real value.
2) Change the situation formula so it reflects an important
condition that should be corrected, and then have a process
to correct that condition.
3) Add Persist setting to the situation formula [in Advanced
button]. That will mean the situation has to occur some number
of times in a row before creating an event. And, of course, have
a process to correct that condition.
--------------------------------------------------------------

EVENTAUDIT1004W
Text: Situations [count] showing event statuses but event not forwarded - see EVENTREPORT008

Meaning: The situations are creating a lot of situation event statuses.
However the events is not forwarded to an event receiver. This may be
normal if no event receiver is used. However if there is an event
receiver like Netcool/Omnibus, this could be a hidden drag on ITM
processing that is hurting performance with no benefit. In some cases
this has been measured at 75% or more of the TEMS incoming workload.

Recovery plan: Review these such situations and see if they are still
needed. If not, stop them and probably delete them.
--------------------------------------------------------------

EVENTAUDIT1005W
Text: Situations [count] showing open->open transitions

Meaning: Normal transitions are open->close->open. Some causes:

1) Missing DisplayItem
2) Duplicate Agent name cases
3) Agent recycled
4) TEMS recycled and Y is from an earlier startup

Details are in EVENTREPORT025.

Recovery plan: Review these such cases and resolve any issues.
--------------------------------------------------------------

EVENTAUDIT1006W
Text: Situations [count] showing close->close transitions

Meaning: Normal transitions are open->close->open. Some causes:
1) Overloaded agent. An agent that does not not repeat results
after 3 sampling intervals will have situation auto-closed by TEMS.
2) Duplicate Agent name cases
3) Agent recycled after a crash.
4) TEMS recycled and N is from an earlier startup

Details are in EVENTREPORT025.

Recovery plan: Review these such cases and resolve any issues.
--------------------------------------------------------------

EVENTAUDIT1007W
Text: Extreme Event Status agents[count] in count instances

Meaning: Sequence number 999 observed in local timestamp. This
can mean the TEMS is overloaded with Situation results. The
result can be TEMS instability including outages and crashes.

See related report EVENTREPORT004 for more comentary.

Recovery plan: Rework the situations to produce fewer events.
--------------------------------------------------------------

EVENTAUDIT1008E
Text: Situations [count] had lodge failures [count]

Meaning: Some situation could not be started because they
had a severe error such as an unknown attribute or a
test value that exceeded the allowed length.

See related report EVENTREPORT007 for more details.

Recovery plan: Correct the situations. Also review the
agent development process to make sure they are tested.
--------------------------------------------------------------

EVENTAUDIT1009W
Text: DisplayItem [sitinfo] with null atomize values situation [sitname] node [agent]

Meaning: DisplayItems are defined to allow the TEMS
to create multiple events for a single evaluation.
In this case a situation with DisplayItem was defined
however a null atomize value was seen. This means that
some events were likely not produced.

That could be a monitoring failure.

On the other hand, if the attribute group involved
could never return multiple results, there is no
bad effect. It is just a little confusing to set a
DisplayItem which is null.

On rare occasions this could related to a X Problem
status in a failed situation startup. See EVENTREPORT006
to cross-check.

Recovery plan: If this is a multi-row situation than
set a DisplayItem for the situation which will allow distinguishing
multiple events. If it is not a multi-row attribute group
than review if the DisplayItem is needed.
--------------------------------------------------------------

EVENTAUDIT1010W
Text: Situations [count] lost events because DisplayItem missing or null Atoms

Meaning: In this circumstance only a single Situation Event
will be created, even though multiple results are present.
Often this is just fine and the extra situation events can
be ignored with no business value.

See Report EVENTREPORT001 for details.

If you want separate Pure situation events at the TEMSes that
agents connect to, there is a TEMS configuration to
force one event per result and is documented in this
document:

ITM Pure Situation events and Event Merging Logic
http://www.ibm.com/support/docview.wss?uid=swg21445309

Recovery plan: If needed, configure the TEMS to force one
situation per result
--------------------------------------------------------------

EVENTAUDIT1011W
Text: Situations [count] lost events because DisplayItem has duplicate atoms

Meaning: Situation can return multiple result rows.

This occurs when occurs when results are returned rapidly.

See EVENTREPORT002 for details;.

In this case, no DisplayItem has been set, even though multiple
results have been seen in the same second. That means that not
all potential situation events will be created.

Incidentally, a DisplayItem is the [up to] first 128 bytes of
another attribute.

Recovery plan: Add proper DisplayItem to situation definition
[Advanced button, DisplayItem in Situation Editor] to specify
a distinguishing attribute. Make sure the DisplayItem is not
constantly changing - as when it contains a date/time stamp.
In such cases the TEMS process size can grow forever and the
TEMS become unstable.

Another option is a TEMS configuration to force pure event one row
for specific attribute tables:

ITM Pure Situation events and Event Merging Logic
http://www.ibm.com/support/docview.wss?uid=swg21445309

--------------------------------------------------------------

EVENTAUDIT1012W
Text: Sampled situations [$tooclose_ct] with events too close for sampling definition

Meaning: Sampled situation will only take a sample at most once every
defined sampling interval. This report shows violation of the case.

See EVENTREPORT006 for details

One observed circumstance is when a situation is composed with
mixed attribute groups one which is Pure [no sampling interval]
and one that is Sampled. This is called a cooerced condition
and does not produce correct results.

Another observed circumstance is when agents are running with
duplicate agent names. This can be on the same system or on
multiple systems reporting to the same remote TEMS. That is
a very bad practice since ITM depends on unique names for agents.
This report can help detect such cases.

Recovery plan: Correct any situations with cooerced situation
formula. Reconfigure any agents with duplicate names. Contact
IBM Support if you need help in this area.
--------------------------------------------------------------

EVENTAUDIT1013W
Text: Situations [count] lost [merged] events Multiple Events with same DisplayItem at same TEMS second

Meaning: When results are processed at the TEMS and
there are multiple ones with same agent, same Situation
and same DisplayItem at the same second TEMS can hide
potential situations.

With Sampled Situations, this is rare unless there are
multiple agents with same name running on the same
agent. That of course must be avoided.


With Pure situations, events can arrive in a flood and
this can happen. The TEMS can be configured to force
one result = one event:

ITM Pure Situation events and Event Merging Logic
http://www.ibm.com/support/docview.wss?uid=swg21445309

Of course you should always consider whether going through
this effort is actually required in such a case, multiple
identical events being processed at the same time should
be reviewed for whether the monitoring is actually necessary.

Recovery plan: Review Pure situation for reasonableness and used
the TEMS configuration if required. For Sampled events, determine
if DisplayItem is giving reasonable results and change if necessary.
--------------------------------------------------------------

EVENTAUDIT1014E
Text: Situations [count] had DisplayItem configured which was not in results

Meaning: Situations had a DisplayItem set. However in the
result attributes coming back, none had that DisplayItem.
As a result the DisplayItem was effectively null which
can result in hidden events.

This was seen when clients were constructing situations
manually instead of using the Situation Editor.

Recovery plan: Correct Situation to supply a correct Displayitem.
--------------------------------------------------------------

EVENTAUDIT1015W
Text: Situations [count] showing irregular open<->close transitions

Meaning: Situations evaluating irregularly. See EVENTREPORT027
for more details.

Recovery plan: Follow plan in EVENTREPORT027.
--------------------------------------------------------------

EVENTAUDIT1016W
Text: Pure situations with results from multiple timestamps [count]

Meaning: Pure situations being merged. See EVENTREPORT028
for more details.

Recovery plan: Follow plan in EVENTREPORT028.
--------------------------------------------------------------

EVENTAUDIT1017I
Text: Situations [$ack_sit] showing Acknowledge/Resurface status

Meaning: This can mean a mis-use of Acknowledge/Resurface and
trigger unneeded concern. See REPORT030 for details.

Recovery plan: Reduce use of Acknowledge unless the issues can
be corrected by the stated time.
--------------------------------------------------------------

EVENTREPORT000
Text: Summary lines

Sample:
EVENTREPORT000: Event/Result Summary Budget Report
Duration: 86273 Seconds
Total Open/Close Events: 3346 2.33/min
Total Results: 264979 184.28/min
Total Non-Forwarded Results: 276 0.19/min [0.10%]
Total Result Bytes: 92873773 63.08 K/min Worry[12.62%]
Total Non-Forwarded Result Bytes: 64005 0.04/min [0.07%]
Sampled Results Confirm: 261862 182.12/min
Sampled Results Confirm Bytes: 83964934 57.03 K/min, 90.41% of total results
Missing DisplayItem: 2839 1.97/min
Duplicate DisplayItem: 49 0.03/min
Null DisplayItem: 3025 97.60/min
Pure Merged Results: 70 0.05/min
Open/Open transitions: 0
Close/Close transitions: 0
Delay Estimate opens[633] over_minimum [228] over_average [1.86 seconds]

Meaning: A quick overall summary of condition.

If negative numbers are seen, there
are likely a lot of event status seen with the same time stamp.

Recovery plan:  none
----------------------------------------------------------------

EVENTREPORT001
Text: Multiple results in one second but DisplayItem missing or null atoms found

Sample:
Situation,Type,Agent_Second,Results,Agent,Atomize,Atom,
kph_ees_wmb_Total_Backouts,Sampled,1140612203045000,11,PACNHB20_BROKER:HB20:KQIB,,,
kph_ees_wmb_Total_Backouts,Sampled,1140612202545000,4,PACNHB21_BROKER:HB21:KQIB,,,
kph_ees_wmb_Total_Backouts,Sampled,1140612202009000,5,PAMBSB20_BROKER:SB20:KQIB,,,

Meaning: This is captured at the agent when there are multiple results present
and the atomize value is null. There may or may not be a DisplayItem value defined
in the situation.

In many cases this causes potential events to be hidden since TEMS will only
generate an event for each unique combination of agent/situation/Displayitem.
In cases like this one will be chosen essentially at randome and displayed.

See EVENTREPORT007 which will display the first two results of one such case
along with a display of which attributes differ.

Recovery plan: If the hidden results are important and should be creating
events, edit the situation formula and add a identifying DisplayItem.
----------------------------------------------------------------

EVENTREPORT002
Text: Multiple results in one second and DisplayItem defined

Sample:
Situation,Type,Agent_Second,Results,Agent,Atomize,Atom,
test_k45_lib_error,Sampled,1120215005726000,3,auusfidb4:45,K45POBJST.ERRCODE,25,
test_k45_lib_error,Sampled,1120215005726000,3,auusfidp4:45,K45POBJST.ERRCODE,25,

Meaning: This is captured at the agent when there are multiple results present
and the DisplayItem is defined but the atomize values are duplicated.

In most cases this causes potential events to be hidden since TEMS will only
generate an event for each unique combination of agent/situation/Displayitem.
In cases like this one will be chosen essentially at randome and displayed.

See EVENTREPORT007 which will display the first two results of one such case
along with a display of which attributes differ.

Recovery plan: If the hidden results are important and should be creating
events, edit the situation formula and Change the DisplayItem to one that
will provide a unique identifier. For example on a Unix OS Agent Process
formula the Process ID will could be used.
----------------------------------------------------------------

EVENTREPORT003
Text: Results at Agent with DisplayItem and null Atom

Sample:
Situation,Type,Agent_Second,Results,Agent,Atomize,Atom,
all_logscrp_x07w_aix_v2,Sampled,1140613104051000,1,czapie22_czapie23:07,K07K07LGS0.LOGFILE,,
all_logscrp_x07w_aix_v2,Sampled,1140612200344000,1,ktazd2787:07,K07K07LGS0.LOGFILE,,
all_logscrp_x07w_aix_v2,Sampled,1140613092857000,1,ktazd3305:07,K07K07LGS0.LOGFILE,,

Meaning: This is captured at the agent when there are multiple results present
and the DisplayItem is defined and some atomize values are null.

In most cases this causes potential events to be hidden since TEMS will only
generate an event for each unique combination of agent/situation/Displayitem.
In cases like this one will be chosen essentially at randome and displayed.

See EVENTREPORT007 which will display the first two results of one such case
along with a display of which attributes differ.

Recovery plan: If the hidden results are important and should be creating
events, edit the situation formula and Change the DisplayItem to one that
will provide a unique identifier. For example on a Unix OS Agent Process
formula the Process ID will could be used.
----------------------------------------------------------------

EVENTREPORT004
Text: Situations with Multiple results at TEMS with same DisplayItem at same second

Sample:
Situation,Type,Agent_Second,Results,Agent,Atomize,Atom,
all_erralrt_x072_aix,Pure,1140612184535000,8,nzapap59:07,K07K07ERL0.DESCRIPTIO,PATH HAS FAILED,
all_erralrt_x072_aix,Pure,1140612185035000,10,nzapap59:07,K07K07ERL0.DESCRIPTIO,PATH HAS FAILED,
all_erralrt_x072_aix,Pure,1140612204536000,13,nzapap59:07,K07K07ERL0.DESCRIPTIO,PATH HAS FAILED,

Meaning: This is captured at the TEMS when there are multiple results present
and the DisplayItem is defined and atomize values are identical.

In most cases this causes potential events to be hidden since TEMS will only
generate an event for each unique combination of agent/situation/Displayitem.
In cases like this one will be chosen essentially at randome and displayed.

See EVENTREPORT007 which will display the first two results of one such case
along with a display of which attributes differ.

Recovery plan: If the hidden results are important and should be creating
events, edit the situation formula and Change the DisplayItem to one that
will provide a unique identifier. For example on a Unix OS Agent Process
formula the Process ID will could be used.
----------------------------------------------------------------

EVENTREPORT005
Text: Situations with Multiple results at Agent with same DisplayItem at same second

Sample:
to be added and clarified.

Meaning: This is captured at the TEMS when there are multiple results present
and the DisplayItem is defined and atomize values are identical.

In most cases this causes potential events to be hidden since TEMS will only
generate an event for each unique combination of agent/situation/Displayitem.
In cases like this one will be chosen essentially at randome and displayed.

See EVENTREPORT007 which will display the first two results of one such case
along with a display of which attributes differ.

Recovery plan: If the hidden results are important and should be creating
events, edit the situation formula and Change the DisplayItem to one that
will provide a unique identifier. For example on a Unix OS Agent Process
formula the Process ID will could be used.
----------------------------------------------------------------

EVENTREPORT006
Text: Timestamps too close together - possible duplicate agents

Sample:
to be added and clarified.

Meaning: to be written

Recovery plan: to be written.
----------------------------------------------------------------

EVENTREPORT007
Text: Detailed Attribute differences on first two merged results

Sample:
Situation,Node,Agent_Time,Reeval,Results,Atom,Atomize,Attribute_Differences
boi_lstnr_grzw_oraext,ASM1:boi_bsswpda1:RZ,1180219084239999,300,2,KRZAGTLSNR.LSNRNAME,LISTENER_SCAN1,KRZAGTLSNR.CONNERRMSG 1[TNS-12560: TNS:protocol adapter error\n] 2[TNS-12541: TNS:no listener\n],KRZAGTLSNR.CONNERROR 1[12560] 2[12541],KRZAGTLSNR.HOSTNAME 1[10.71.73.106] 2[ ],KRZAGTLSNR.PORT 1[1924] 2[-1],KRZAGTLSNR.PROTOCOL 1[TCPS] 2[IPC],KRZAGTLSNR.SERVICEKEY 1[ ] 2[LISTENER_SCAN1],KRZAGTLSNR.TESTTIME 1[1180219083635000] 2[1180219083636000],,
boi_serresp_gynw_boiwas9,AppSrv01SOA:boi_vm000000467:KYNS,1180219091622999,90,2,KYNSERVLT.SERVER_NAM,SOAServer1,KYNSERVLT.APPL_NAME 1[projections-webservices-ear] 2[BIL Quotes NBQ UI EAR],KYNSERVLT.AVG_RT 1[936000] 2[1030000],KYNSERVLT.SVLT_NAME 1[webservices] 2[NBQ_SPRING_SERVLET],KYNSERVLT.WAR_NAME 1[projections-webservices-1.0.war] 2[projections-nbq-1.0.war],,

Meaning: When you see an advisory on merged results, this report
will show what attributes were different for the first two result
instances. Only a single case of situation/agent is shown although
multiple cases are usually involved. In some cases this will let you
decide what the DisplayItem should be.

Recovery plan: Correct the situaton so results transform into
individual situation events with proper use of DisplayItem.
----------------------------------------------------------------



EVENTREPORT011
Text: Event/Results Budget Situations Report by Result Bytes

Sample
Situation,Table,Rowsize,Reeval,Event,Event%,Event/min,Results,ResultBytes,Result%,Miss,MissBytes,Dup,DupBytes,Null,NullBytes,SampConfirm,SampConfirmBytes,PureMerge,PureMergeBytes,transitions,nodes,PDT
kph_soa_Slow_Transactions,AGGREGATS,3368,300,1232,19.88%,0.86,85715,288688120,60.26%,32,107776,58,195344,0,0,85065,286498920,56,188608,1232,4,*IF *VALUE Aggregates.Group_Level *EQ Transaction *AND *VALUE Aggregates.Total_Time_Deviation *GT 100,
kph_soa_Failed_Transactions,AGGREGATS,3368,300,106,1.71%,0.07,11693,39382024,8.22%,28,94304,50,168400,0,0,11609,39099112,47,158296,106,1,*IF *VALUE Aggregates.Group_Level *EQ Transaction *AND *VALUE Aggregates.Percent_Failed *GT 50,
kph_soa_Transaction_Rate_W,TOINTSIT,500,300,706,11.39%,0.49,56320,28160000,5.88%,333,166500,990,495000,0,0,55179,27589500,12,6000,706,4,*IF *VALUE Interaction_Situations.Display_Format *EQ '${DestinationContext.ComponentName} - ${DestinationContext.ServerName}' *AND *VALUE Interaction_Situations.Metric_Name *EQ DeviationTransactionRate *AND *VALUE Interaction_Situations.Metric_Value *GT 50 *AND *VALUE Interaction_Situations.Metric_Value *LE 100,
Meaning: Report what situation created the most situation events

Sorted in reverse number by the number of result bytes observed. This report
only counts Open [Y] and ignores others because those are not associated with
specific agents.

Situation,Table,Rowsize,Reeval,Event,Event%,Event/min,Results,ResultBytes,Result%,Miss,MissBytes,Dup,DupBytes,Null,NullBytes,SampConfirm,SampConfirmBytes,PureMerge,PureMergeBytes,transitions,nodes,PDT
kph_soa_Slow_Transactions,AGGREGATS,3368,300,1232,19.88%,0.86,85715,288688120,60.26%,32,107776,58,195344,0,0,85065,286498920,56,188608,1232,4,*IF *VALUE Aggregates.Group_Level *EQ Transaction *AND *VALUE Aggregates.Total_Time_Deviation *GT 100,
kph_soa_Failed_Transactions,AGGREGATS,3368,300,106,1.71%,0.07,11693,39382024,8.22%,28,94304,50,168400,0,0,11609,39099112,47,158296,106,1,*IF *VALUE Aggregates.Group_Level *EQ Transaction *AND *VALUE Aggregates.Percent_Failed *GT 50,
kph_soa_Transaction_Rate_W,TOINTSIT,500,300,706,11.39%,0.49,56320,28160000,5.88%,333,166500,990,495000,0,0,55179,27589500,12,6000,706,4,*IF *VALUE Interaction_Situations.Display_Format *EQ '${DestinationContext.ComponentName} - ${DestinationContext.ServerName}' *AND *VALUE Interaction_Situations.Metric_Name *EQ DeviationTransactionRate *AND *VALUE Interaction_Situations.Metric_Value *GT 50 *AND *VALUE Interaction_Situations.Metric_Value *LE 100,

PureMerge,PureMergeBytes,transitions,nodes,PDT
Situation        : Situation Name. This can be the name index in case TNAME Fullname is used
Table            : Attribute Table Name
Rowsize          : Estimated result row size
Reeval           : Reevaluation or sampling time in seconds. Zero means a Pure situation
Event            : Number of new situation events
Event%           : Per Cent of total Events observed
Results          : Number of situation result rows
ResultBytes      : Estimated number of size of all result rows
Results%         : Per Cent of total result row sizes
Miss             : Results missed because no DisplayItem
MissBytes        : Estimated size of all Missed events
Dup              : Results missed because DisplayItem with duplicate atomize values
DupBytes         : Estimated size of all Duplicate atomize value cases
Null             : Results missed because DisplayItem had a null atomize
NullBytes        : Estimated size of all Null Atomize values
Miss             : Results missed because no DisplayItem
MissBytes        : Estimated size of all Missed events
Miss             : Results missed because no DisplayItem
MissBytes        : Estimated size of all Missed events
SampConfirm      : Results which confirm each open Sampled Situation event
SampConfirmBytes : Estimated size of all confirm results
PureMerge        : Results which were merged by TEMS because Pure situation results arrived at same second at TEMS
PureMergeBytes   : Estimated size of all merged Pure Situation Results
Transitions      : Transitions from one open to close or reverse
Nodes            : Number of reporting nodes [agents]
PDT              : Situation Formula [predicate]

There are savings to be had be reducing the number of situations event statuses.
The benefit is both at the remote TEMS and the hub TEMS.

Recovery plan:  Review report and improve TEMS efficiency by eliminating
or redesigning the situation workloads.
----------------------------------------------------------------

EVENTREPORT012
Text: Budget Report by Thrunode

Sample
Thrunode,Event,Event%,Event/min,Results,ResultBytes,Result%,Miss,MissBytes,Dup,DupBytes,Null,NullBytes,SampConfirm,SampConfirmbytes,PureMerge,PureMergeBytes,transitions,
ASYS:CMS,1,0.02%,0.00,123,8856,0.00%,0,0,0,0,0,0,122,8784,0,0,
CSYS:CMS,14,0.23%,0.01,2733,894607,0.19%,0,0,0,0,0,0,2725,892358,0,0,
HUB_2990BU,1,0.02%,0.00,795,397500,0.08%,0,0,0,0,0,0,794,397000,0,0,

See EVENTREPORT001 for definitions of the Columns

Meaning: Much like EVENTREPORT011 but is shows how results are arriving from different remote TEMSes
This is only interesting when Event Audit is run on a hub TEMS.

If the is a large imbalance it may be useful to balanace the agents between
the different remote TEMSes/

Recovery plan:  Review report and improve TEMS efficiency by eliminating
or redesigning the situation workloads.
----------------------------------------------------------------

EVENTREPORT013
Text: Budget Report by Node

Sample
EVENTREPORT013: Budget Report by Node
Node,Event,Results,ResultBytes,Result%,Miss,MissBytes,Dup,DupBytes,Null,NullBytes,SampConfirm,SampConfirmbytes,PureMerge,PureMergeBytes,transitions,delay[count/min/mode/avg/max],
czzpms1e:TO,640,10.33%,0.45,44613,127303980,26.57%,94,49868,245,128236,0,0,44085,126277092,4,7736,640,[322/0/0/0.05/1],
czzpms1f:TO,721,11.64%,0.50,65138,123932008,25.87%,103,212108,347,460300,0,0,64561,123024020,105,324960,721,[361/0/0/0.16/1],

See EVENTREPORT001 for definitions of the Columns

Meaning: Much like EVENTREPORT011 but is shows how results are arriving from different Agents.

If there is a large imbalance, it may be useful to review the heavy agent
contributors to work to reduce there workload.

Recovery plan:  Review report and improve TEMS efficiency by eliminating
or redesigning the situation workloads.
----------------------------------------------------------------

EVENTREPORT016
Text: Delay Report by Node and Situation

Sample
EVENTREPORT016: Delay Report by Node and Situation
Node,Situation,Atomize,Delay,Min_delay,
DEV3_Member1:wzadwa3:KYNS,kph_wasappsvr_gync_was_base,DEV3_Member1,12,0,1140612170134001,
DEV3_Member2:wzadwa3:KYNS,kph_wasappsvr_gync_was_base,DEV3_Member2,12,0,1140612170134000,


Meaning: This reports cases where the delay between agent producing the data is more than
one second. Typical well running environments show 0 or 1 second measurements. This could
indicate a remote TEMS under stress, or a agent system under stress or network issues or
even a clock time difference between agent and TEMS.

Recovery plan:  Investigate TEMS and agent and take corrective actions.
----------------------------------------------------------------

EVENTREPORT017
Text: Extreme event arrival report SEQ999

Sample:
Situation,Count,Nodes,Times
CIB_UNIX_Disk_RW_Pct_H,2325,132,1171221040312999[35] 1171221035712999[33] ...
CIB_UNIX_Page_Scan_Pct_H,2215,307,1171221032108999[47] 1171221031908999[44] ...

Situation    : Situation Name. This can be the name index in case TNAME Fullname is used
Count        : Number of extreme arrival events
Nodes        : Number of nodes where extreme arrival observed
Times        : Time [local time at agent when data filtered] and count of how many seen

Meaning: TEMS creates a time stamp for arriving situation event statuses.
CYYMMDDHHMMSSTTT The last three characters are a sequence number. When more than
1000 situation events arive in a single second, the fixed number 999 is used.

This is sometimes normal such as during a TEMS startup. However if the
condition is frequent, it usually means the TEMS is being overwhelmed with
situation result data and may become unstable. Situations should report on
rare events and not common conditions.

For example the second situation CIB_UNIX_Page_Scan_Pct_H formula was

*IF *VALUE Unix_Memory.Page_Scan *GE 30

At this site, the condition was so common at 307 agents that situation events were
constantly opening and closing. This caused excessive workload at the TEMS and
was one factor that caused TEMS instability.

Recovery plan: Redesign the situation to avoid these extreme cases.
----------------------------------------------------------------

EVENTREPORT019
Text: Segmented arrival report SEQ998

Sample:
[add later]

Situation    : Situation Name. This can be the name index in case TNAME Fullname is used
Count        : Number of extreme arrival events
Nodes        : Number of nodes where extreme arrival observed
Times        : Time [local time at agent when data filtered] and count of how many seen

Meaning: TEMS creates a time stamp for arriving situation event statuses.
CYYMMDDHHMMSSTTT The last three characters are a sequence number.

There are rare cases where situation result data has to be segmented into multiple rows.
In this case the last sequence number is 998. This condition is not well understood and
is also pretty rare. Thus a report section was added to aid studying issue.

Recovery plan: Work to understand why segmented arrival is occurring.
----------------------------------------------------------------

EVENTREPORT020
Text: Deltastat X (Problem) Report

Sample:
Situation,Count,Nodes,Times
ddb_fss_xuxc_ws,3,

Meaning: This Situation had some serious error can could not run.
TEMS assigns a status of X and does not run it.

Recovery plan: Correct the situaton so it works. The diagnostic log
will contain details about the error.
----------------------------------------------------------------

EVENTREPORT998
Text: List of estimated table sizes

Sample:
Table,Count,
K07K07ERL0,26,
QMEVENTC,4,
TOINTSIT,215,

Meaning: The Event Audit program has a large built in table of
Attibute Row Table sizes. These are ones which were discovered
in the TSITSTSH information but were not in the table. Over time
product tables will be added. There can also be Agent Builder or
Universal Agent tables spotted which are used defined. By default
the size is assumed to be 500 bytes if not found.

Recovery plan: information only
----------------------------------------------------------------

EVENTREPORT999
Text: Full report sorted by Node/Situation/Time

Sample:
Situation,Node,Thrunode,Agent_Time,TEMS_Time,Deltastat,Reeval,Results,Atomize,DisplayItem
boi_lstnr_grzw_oraext,ASM1:boi_bsswpda1:RZ,REMOTE_t02rt12px,1180219083739999,1180219084057044,N,300,0,KRZAGTLSNR.LSNRNAME,LISTENER_SCAN1,
boi_lstnr_grzw_oraext,ASM1:boi_bsswpda1:RZ,REMOTE_t02rt12px,1180219084239999,1180219084239001,Y,300,2,KRZAGTLSNR.LSNRNAME,LISTENER_SCAN1,
,,,,,,,1,*PREDICATE=KRZAGTLSNR.STATUS = 2 ;KRZAGTLSNR.ADDRESS=(PROTOCOL=TCPS)(HOST=10.71.73.106)(PORT=1924);KRZAGTLSNR.CONNERRMSG=TNS-12560: TNS:protocol adapter error\n;KRZAGTLSNR.CONNERROR=12560;KRZAGTLSNR.HOSTNAME=10.71.73.106;KRZAGTLSNR.LSNRFILE=/u01/app/12.1.0/grid/network/admin/listener.ora;KRZAGTLSNR.LSNRNAME=LISTENER_SCAN1;KRZAGTLSNR.ORIGINNODE=ASM1:boi_bsswpda1:RZ;KRZAGTLSNR.PIPENAME= ;KRZAGTLSNR.PORT=1924;KRZAGTLSNR.PROTOCOL=TCPS;KRZAGTLSNR.SERVICEKEY= ;KRZAGTLSNR.STATUS=2;KRZAGTLSNR.TESTTIME=1180219083635000;KRZAGTLSNR.TIMESTAMP=1180219084112000,
,,,,,,,2,KRZAGTLSNR.ADDRESS=(PROTOCOL=IPC)(KEY=LISTENER_SCAN1);KRZAGTLSNR.CONNERRMSG=TNS-12541: TNS:no listener\n;KRZAGTLSNR.CONNERROR=12541;KRZAGTLSNR.HOSTNAME= ;KRZAGTLSNR.LSNRFILE=/u01/app/12.1.0/grid/network/admin/listener.ora;KRZAGTLSNR.LSNRNAME=LISTENER_SCAN1;KRZAGTLSNR.ORIGINNODE=ASM1:boi_bsswpda1:RZ;KRZAGTLSNR.PIPENAME= ;KRZAGTLSNR.PORT=-1;KRZAGTLSNR.PROTOCOL=IPC;KRZAGTLSNR.SERVICEKEY=LISTENER_SCAN1;KRZAGTLSNR.STATUS=2;KRZAGTLSNR.TESTTIME=1180219083636000;KRZAGTLSNR.TIMESTAMP=1180219084112000,

Meaning: Report what situation created the most situation event statuses.

Sorted in Node then Situation then TEMS Time order. This section can be used to
understand exactly what conditions were observed. The sorting time is the TEMS
time, not the agent time.

If multiple results are present in the situation event history, you will see the
details of each result segment is presented. A row may start with *PREDICATE
which is a summary of the situation formula.


Situation    : Situation Name. This can be the name index in case TNAME Fullname is used
Node         : Agent name
Thrunode     : Which system received and processed the results, usually a hub or remote TEMS
Agent_Time   : Time when situation status was observed at the agent in ITM time format CYYMMDDHHMMSSXXX
TEMS_Time    : Time when situation status was observed at the TEMS in ITM time format CYYMMDDHHMMSSXXX
Deltastat    : Y for Open and N for Close
Reeval       : Situation Samplinging interval - zero means a pure situation
Results      : The number of observed result segments in this TEMS second
Atomize      : Value of atomize if any for this
DisplayItem  : The attribute used for atomize in attribute_group_table.attribute_column form

In the list of attributes, the first ones associated with the the Situation Predicate and afterwards
all of the attributes.

Recovery plan:  Use report to help understand the summary reports.
----------------------------------------------------------------

EVENTREPORT003
Text: Event Summary sorted by Transitions

Sample:
Situation,Count,Count%,Count/min,Open,Close,Sampled,Sampled%,Sampled/min,Pure,Pure%,Pure/min,Atomize,Atoms,Nodes,Transitions,Tr/hour,PDT
boi_logscrp_g06c_win,5549,75.17%,69.18,5533,16,145,0.66%,1.81,0,0.00%,0.00,,1,14,31,23.19,*IF *VALUE K06_LOGFILEMONITOR_SCRIPT.RC *NE '17' *UNTIL ( *TTL 0:00:05:00 ),
boi_prcmis_xuxc_ctrlmsprc,222,1.47%,2.77,108,114,4816,21.82%,60.04,0,0.00%,0.00,UNIXPS.UCOMMAND,6,2,216,161.56,*IF *MISSING Process.Process_Command_U *EQ ('*p_ctmsu*','*p_ctmrt*','*p_ctmns*','*p_ctmtr*','*p_ctmwd*','*p_ctmca*') *UNTIL ( *TTL 0:00:05:00 ),

Meaning: Report what situation created the most situation events

Sorted in reverse number by the number of status transitions status. This means
Open [Y] to Close [N] or  Close[N] to Open [Y]. The goal is to identify situation
experiencing many open/close/open/close sequences. Those cases are wasteful and
violate the ITM goal that situation events be rare and exceptional and repairable.

See EVENTREPORT001 for definitions of the Columns

Recovery plan:  Review report and improve TEMS efficiency by eliminating
or redesigning the situation workloads.
----------------------------------------------------------------

EVENTREPORT008
Text: List of estimated table sizes

Sample:
to be added

Meaning: Result byte calculations depend on a built in table
and values supplied in the eventaud.ini file. If tables are
not found, they are assigned a length of 500 bytes. This
includes Agent Builder and Universal Agent agents, but also
includes ones not found in development.

Recovery plan:  Add control to eventaud.ini to increase report
accuracy.
----------------------------------------------------------------

EVENTREPORT009
Text: Incoming workload sorted by time

Sample:
no be added

Meaning: Detailed report on counts and result rows overall by time

Needs the -time option to be produced. Rather a lot of output.

Recovery plan:  Used to research workload in depth.
----------------------------------------------------------------

EVENTREPORT010
Text: Incoming workload sorted by Time and Thrunode

Sample:
no be added

Meaning: Detailed report on counts and result rows overall by time

Needs the -time option to be produced. Rather a lot of output.

Recovery plan:  Used to research workload in depth.
----------------------------------------------------------------

EVENTREPORT011
Text: Incoming workload sorted by Time and Node

Sample:
no be added

Meaning: Detailed report on counts and result rows overall by time

Needs the -time option to be produced. Rather a lot of output.

Recovery plan:  Used to research workload in depth.
----------------------------------------------------------------

EVENTREPORT012
Text: Incoming workload sorted by Time and Situation

Sample:
no be added

Meaning: Detailed report on counts and result rows overall by time

Needs the -time option to be produced. Rather a lot of output.

Recovery plan:  Used to research workload in depth.
----------------------------------------------------------------

EVENTREPORT013
Text: Incoming workload sorted by Time and Situation

Sample:
no be added

Meaning: Detailed report on counts and result rows overall by time

Needs the -time option to be produced. Rather a lot of output.

Recovery plan:  Used to research workload in depth.
----------------------------------------------------------------

EVENTREPORT014
Text: Incoming workload sorted by Time and Situation

Sample:
no be added

Meaning: Detailed report on counts and result rows overall by time

Needs the -time option to be produced. Rather a lot of output.

Recovery plan:  Used to research workload in depth.
----------------------------------------------------------------

EVENTREPORT015
Text: Incoming workload sorted by Time and Situation

Sample:
no be added

Meaning: Detailed report on counts and result rows overall by time

Needs the -time option to be produced. Rather a lot of output.

Recovery plan:  Used to research workload in depth.
----------------------------------------------------------------

EVENTREPORT016
Text: Incoming workload sorted by Time and Situation

Sample:
no be added

Meaning: Detailed report on counts and result rows overall by time

Needs the -time option to be produced. Rather a lot of output.

Recovery plan:  Used to research workload in depth.
----------------------------------------------------------------

EVENTREPORT017
Text: Multiple results in one second but DisplayItem missing or null atoms found

Sample:
no be added

Meaning: Detailed report on counts and result rows overall by time

Needs the -time option to be produced. Rather a lot of output.

Recovery plan:  Used to research workload in depth.
----------------------------------------------------------------

EVENTREPORT018
Text: Situations processed but not forwarded

Sample:
Situation,Count,Nodes,
SysPerf_avg_process_usage,159,43,
SysPerf_processor_usage,811,64,
ESM_PRF_linux_processcpu_usage,99,14,

Meaning: Some situation events are forwarded but not these ones. This
may be excess work if no one is reviewing the situation events.

Recovery plan:  Consider forwarding the event or stopping the situation.
----------------------------------------------------------------

EVENTREPORT019
Text: Multiple results in one second DisplayItem defined

Sample:
no be added

Meaning: Detailed report on counts and result rows overall by time

Needs the -time option to be produced. Rather a lot of output.

Recovery plan:  Used to research workload in depth.
----------------------------------------------------------------

EVENTREPORT024
Text: Situations using unknown DisplayItems

Sample:
Situation,DisplayItem,
ccp_fss_ulzf_suse,KLZDISK.MOUNTPT,

Meaning: Detailed report on situations which used unknown DisplayItems.
In this example case the agent was actually returning LNXDISK.MOUNTPT=/

Recovery plan:  Correct the situations.
----------------------------------------------------------------

EVENTREPORT025
Text: Situations showing Open->Open and Close->Close Statuses

Sample:
Situation,Type,Count,Node_ct,Nodes,
CONTECAR_Proceso_Caido,NN,3,1,spcitm:2P,
DNS_Response_Time_Critical,NN,25,1,SPRCADSB:3Z,
DNS_Total_Dyn_Update_Warning,NN,1,1,SPRCADSP:3Z,
JMX_HeapMemoryUsageHigh,YY,1,1,TOSTTS-CNR:spcitm:1J,
JMX_HeapMemoryUsageHigh,NN,79,7,GEOROUTING-CNR:spcitm:1J GEOROUTING-SPC:spcitm:1J IPASERVER:spcitm:1J  ....

Meaning: Repeated Close [N] or Open [Y] statuses in sampled situations
can be normal. This will be seen for example if an agent is recycled

If this occurs a lot, it may indicate several bad possibilities:

A) Agent is having problems and connecting over and over again
B) Duplicate Agents are installed and reporting to the same
remote TEMS. This can be on different systems or even on the
same system.
C) There can be an agent malconfiguration, such as conflicting
use of KDEB_INTERFACELIST exclusive/anonymous bind and occasionally
a rare use of KDCB0_HOSTNAME which overrides KDEB_INTERFACELIST.

Recovery plan: Investigate the agents involved and correct issues.
----------------------------------------------------------------

EVENTREPORT026
Text: Situations showing high Open<->Close rate

Sample:
Situation,Reeval,Rate,Node_ct,PDT
Linux_Disk_Space_Critical,600,1.45,1,*IF ( ( *VALUE Linux_Disk.Mount_Point *EQ '/' *AND *VALUE Linux_Disk.Space_Used_Percent *GE 98 ) *OR ( *VALUE Linux_Disk.Mount_Point *EQ '/opt' *AND *VALUE Linux_Disk.Space_Used_Percent *GE 98 ) *OR ( *SCAN Linux_Disk.Mount_Point *EQ '/opt/IBM' *AND *VALUE Linux_Disk.Space_Used_Percent *GE 98 *AND *VALUE Linux_Disk.System_Name *NE tnm01alp ) *OR ( *VALUE Linux_Disk.Mount_Point *EQ '/tmp' *AND *VALUE Linux_Disk.Space_Used_Percent *GE 98 ) *OR ( *VALUE Linux_Disk.Mount_Point *EQ '/var' *AND *VALUE Linux_Disk.Space_Used_Percent *GE 98 ) *OR ( *VALUE Linux_Disk.Mount_Point *EQ '/home' *AND *VALUE Linux_Disk.Space_Used_Percent *GE 95 ) ),
CPU_Greater_Than_50_Pct,300,1.81,2,*IF *VALUE Linux_CPU.CPU_ID *EQ Aggregate *AND *VALUE Linux_CPU.Idle_CPU *LE 50.00,

Meaning: The situations named are steadily going open and then closed.
This is an indication that the condition is not rare and is not
being fixed. If no one cares enough to fix the issue, the situation
formula should be altered to something meaningful or just stopped
and deleted as waste of time.

You do see some active helper situations, like whether the time
as at a certain point. This is often not best practice. You have
to ask yourself why would you ever want to wait for an alert - if
it is Rare, Exceptional and Fixable.

If you want to record data at fixed points in time, like every
15 minutes, consider using historical data collection which is
works exactly that way and does not bog down the TEMSes if the
data is collected at the agents.

Recovery plan: Investigate the situations involved and determine
if they are really useful.
----------------------------------------------------------------

EVENTREPORT027
Text: Sampled situations with iregular Open<->Close processing times

Sample:
Situation,Reeval,YNY_Count,Non_Zero_diffs,
A_Sched_Citrix_355a_430a_AllDay,300,60,-3[4] -2[9],
A_Schedule_AspireApp_Window,300,20,-69[10],
A_Schedule_Goxsa2140_Window,300,2,-114[1] 43[1],

Meaning: The situations named show some cases where the Open to
Close or Close to Open contradicts the sampling interval. In a
well running TEMS, the times should always be an even multiple
of the sampling interval.

Differences could mean a TEMS under workload stress or stress
from other processes in the same environment. If there are
a large number of them it might indicate a duplicate agent
condition.

This has more meaning when run on a remote TEMS or a single
hub TEMS. When a hub TEMS has remote TEMS, each are operating
separately and the combined event history is as specific.

Recovery plan: Investigate the conditions for other evidence
of high workload. duplicate agents or other stressful conditions.
If necessary reduce workload by rebalancing workload to other
TEMSes or other means.
----------------------------------------------------------------

EVENTREPORT028
Text: Pure situations with results from multiple timestamps [count] cases

Sample:
Situation,Node,Thrunode,Table,Atomize,TEMS_Time,Agent_Count,Agent_Times,
UHT_FSMON_MINOR,LO:wmbm8023_fsmon,RMT_ELR_apsrp06285,KLOLOGPEVT,/opt,1180707175633000,2,1180707130128000[1] 1180707130157000[1],
UHT_FSMON_MINOR,LO:wmbm8023_fsmon,RMT_ELR_apsrp06285,KLOLOGPEVT,/opt,1180707175634000,8,1180707140128000[1] 1180707140157000[1] 1180707150128000[1] 1180707150157000[1] 1180707160128000[1] 1180707160157000[1] 1180707170128000[1] 1180707170157000[1],


Meaning: The Pure situations involved are creating situation
events. However additional results are being "merged" and thus
an event receiver will never see them.

Sometimes you can use a DisplayItem to force uniqueness. However
you can see in the sample cases that is not always sufficient.

One possibility is that the TEMS receiving the data is extremely
overloaded and when the process to create the situation runs,
multiple events are seen. That could be true in the first sample
above where 29 seconds elapsed between the first and second sample.

A more general solution is to configure each TEMS involved to
perform Pure Event One Row logic. That forces TEMS to make a
separate situation event from each pure result for the named
application and table name. See the following for details.

ITM Pure Situation events and Event Merging Logic
http://www.ibm.com/support/docview.wss?uid=swg21445309

Recovery plan: Investigate condition and resolve.
----------------------------------------------------------------

EVENTREPORT029
Text: Event totals per Situation/Agent

Sample:
Situation,Node,Events,
ITM_Transaction_VP,CO01VCANSOF:T6,1756,
UDB_Agent_DM_Down,prdb2i1:co01bpmdb:UD,1524,
RRT_Response_Time_War,CO01VCANSOF:T6,249,

Meaning: This reports on the total number of situation open
events arriving from agents. These all have to be processed
by the TEPS and possibly sent to an event receiver.

In some cases this has detected situation events that were
"invisible" because they were not sent to an event receiver
and not associated to any TEP navigation node. In that case
the processing just burned resources with no value and also
slowed TEPS processing.

Recovery plan: Review situations and stop ones that are not
useful.
----------------------------------------------------------------

EVENTREPORT030
Text: Sampled situations with Acknowledge/Resurface Status

Sample:
Situation,ACK_ct,RES_ct,ACK_Time,YA_ct,AF_ct,FA_ct,FN_ct
ccp_ms_offline,383,359,7697671,17,167,162,3,
ccp_swapprc_rlzw_stdv2,7,5,305726,2,2,1,0,
ccp_gpfsscrp_g70f_gpfs,10,10,220996,1,5,4,0,

Meaning: This reports on the conditions where the
Acknowledge function was used on a situation event. That
means the event was temporarily hidden. The Acknowledge
is an statement that the condition will be corrected in
a stated amount of time. When that time ends, the situation
is evaluated again. If the condition is now corrected, a
close Situation event is seen. If it still exists, a
status F [Resurface] is generate to record the condition
still needs to be corrected.

ACK_ct: count of Acknowledgements
RES_ct: count of Resurfaces
ACK_time: total seconds the situation was in Acknowledge status
YA_ct: count of Y [True] to A [Acknowledge] transitions
AF_ct: count of A [Acknowledge] to F [Resurface] transitions
FA_ct: count of F [Resurface] to A [Acknowledge] transitions
FN_ct: count of F [Resurface] to N [Close] transitions

The report is sorted in descending time by the seconds in
Acknowledge state.

In the customer case which inspired this report section,
the customer was unaware of the Netcool generated Acknowledge
logic. As a result certain agents were going offline and later
online repeatedly without other explanation. In most cases
the agent offline condition was not corrected and the resulting
flood of tickets was a serious problem.

Recovery plan: Review situations and Acknowledge usage.
----------------------------------------------------------------

EVENTREPORT031
Text: Nodes with situations with Acknowledge/Resurface Status

Sample:
Node,ACK_ct,RES_ct,ACK_Time,YA_ct,AF_ct,FA_ct,FN_ct,Situations,
gct_es0311gct5018:KUL,28,27,1487607,1,27,27,0,ccp_ms_offline[27],
gct_es0311gct200d:KUL,27,26,1383518,1,26,26,0,ccp_ms_offline[26],

Meaning: This reports on the conditions where the
Acknowledge function was used on a situation event. That
means the event was temporarily hidden. The Acknowledge
is an statement that the condition will be corrected in
a stated amount of time. When that time ends, the situation
is evaluated again. If the condition is now corrected, a
close Situation event is seen. If it still exists, a
status F [Resurface] is generate to record the condition
still needs to be corrected.

ACK_ct: count of Acknowledgements
RES_ct: count of Resurfaces
ACK_time: total seconds the situation was in Acknowledge status
YA_ct: count of Y [True] to A [Acknowledge] transitions
AF_ct: count of A [Acknowledge] to F [Resurface] transitions
FA_ct: count of F [Resurface] to A [Acknowledge] transitions
FN_ct: count of F [Resurface] to N [Close] transitions
Situations: The situations involved in the Acknowledge/Resurface

The report is sorted in descending time by the seconds in
Acknowledge state.

The Situation Status History is a limited wrap-around table
and so the list will not be exhaustive. See EVENTREPORT030
for more details.


Recovery plan: Review situations and Acknowledge usage.
----------------------------------------------------------------

EVENTREPORT032
Text: Event/Results Budget Situations Report by Events

Sample:
Situation,Table,Rowsize,Reeval,Event,Event%,Event/min,Results,ResultBytes,Result%,Miss,MissBytes,Dup,DupBytes,Null,NullBytes,SampConfirm,SampConfirmBytes,PureMerge,PureMergeBytes,transitions,nodes,PDT
wbc_VIOS-Process-duplicate_aix_va_warning_std,KVA32PROCE,2732,30,1653,47.00%,6.19,258917,707361244,86.91%,0,0,0,0,0,0,258917,707361244,0,0,1653,61,*IF *COUNT KVA_PROCESSES_DETAIL.Process_Name *GE '1' *AND *VALUE KVA_PROCESSES_DETAIL.Process_Name *EQ 'aixDataProvider-61',
wbc_VIOS-physical-memory-percent-used-is-high_aix_va_warning_std,KVA27PHYSI,84,60,331,9.41%,1.24,22434,1884456,0.23%,0,0,0,0,0,0,22434,1884456,0,0,331,38,*IF *VALUE KVA_PHYSICAL_MEMORY.Used_Memory_Pct *GE 90,

Meaning: This reports on the conditions where the
Acknowledge function was used on a situation event. That
means the event was temporarily hidden. The Acknowledge
is an statement that the condition will be corrected in
a stated amount of time. When that time ends, the situation
is evaluated again. If the condition is now corrected, a
close Situation event is seen. If it still exists, a
status F [Resurface] is generate to record the condition
still needs to be corrected.

ACK_ct: count of Acknowledgements
RES_ct: count of Resurfaces
ACK_time: total seconds the situation was in Acknowledge status
YA_ct: count of Y [True] to A [Acknowledge] transitions
AF_ct: count of A [Acknowledge] to F [Resurface] transitions
FA_ct: count of F [Resurface] to A [Acknowledge] transitions
FN_ct: count of F [Resurface] to N [Close] transitions
Situations: The situations involved in the Acknowledge/Resurface

The report is sorted in descending time by the seconds in
Acknowledge state.

The Situation Status History is a limited wrap-around table
and so the list will not be exhaustive. See EVENTREPORT030
for more details.


Recovery plan: Review situations and Acknowledge usage.
----------------------------------------------------------------

EVENTREPORT032
Text: Event/Results Budget Situations Report by Events

Sample:
Situation,Table,Rowsize,Reeval,Event,Event%,Event/min,Results,ResultBytes,Result%,Miss,MissBytes,Dup,DupBytes,Null,NullBytes,SampConfirm,SampConfirmBytes,PureMerge,PureMergeBytes,transitions,nodes,PDT
wbc_VIOS-Process-duplicate_aix_va_warning_std,KVA32PROCE,2732,30,1653,47.00%,6.19,258917,707361244,86.91%,0,0,0,0,0,0,258917,707361244,0,0,1653,61,*IF *COUNT KVA_PROCESSES_DETAIL.Process_Name *GE '1' *AND *VALUE KVA_PROCESSES_DETAIL.Process_Name *EQ 'aixDataProvider-61',
wbc_VIOS-physical-memory-percent-used-is-high_aix_va_warning_std,KVA27PHYSI,84,60,331,9.41%,1.24,22434,1884456,0.23%,0,0,0,0,0,0,22434,1884456,0,0,331,38,*IF *VALUE KVA_PHYSICAL_MEMORY.Used_Memory_Pct *GE 90,
Text: Event/Results Budget Situations Report by Result Bytes

Sorted in reverse number by the number of events observed. This report counts
opens and closes.

Situation        : Situation Name. This can be the name index in case TNAME Fullname is used
Table            : Attribute Table Name
Rowsize          : Estimated result row size
Reeval           : Reevaluation or sampling time in seconds. Zero means a Pure situation
Event            : Number of new situation events
Event%           : Per Cent of total Events observed
Results          : Number of situation result rows
ResultBytes      : Estimated number of size of all result rows
Results%         : Per Cent of total result row sizes
Miss             : Results missed because no DisplayItem
MissBytes        : Estimated size of all Missed events
Dup              : Results missed because DisplayItem with duplicate atomize values
DupBytes         : Estimated size of all Duplicate atomize value cases
Null             : Results missed because DisplayItem had a null atomize
NullBytes        : Estimated size of all Null Atomize values
Miss             : Results missed because no DisplayItem
MissBytes        : Estimated size of all Missed events
Miss             : Results missed because no DisplayItem
MissBytes        : Estimated size of all Missed events
SampConfirm      : Results which confirm each open Sampled Situation event
SampConfirmBytes : Estimated size of all confirm results
PureMerge        : Results which were merged by TEMS because Pure situation results arrived at same second at TEMS
PureMergeBytes   : Estimated size of all merged Pure Situation Results
Transitions      : Transitions from one open to close or reverse
Nodes            : Number of reporting nodes [agents]
PDT              : Situation Formula [predicate]

There are savings to be had be reducing the number of situations event statuses.
The benefit is both at the remote TEMS and the hub TEMS.

Recovery plan:  Review report and improve TEMS efficiency by eliminating
or redesigning the situation workloads.
----------------------------------------------------------------

EVENTREPORT033
Text: Situations Open for long periods of time sorted by Cache Usage

Sample:
Situation,Open,Close,Cache,Cache_pc,Cache_cum,Open_secs,Elapsed,Open-pc,Nodes,Reeval,PDT
all_i0708wd_gnth_win,434,296,139,6.33%,6.33%,20901628,21930920,95.31%,139,300,*IF *VALUE Local_Time.Hours *NE 07,
all_i2008sd_gnth_win,136,136,135,6.15%,12.48%,4357518,4358718,99.97%,135,300,*IF *VALUE Local_Time.Hours *GE 08 *AND *VALUE Local_Time.Hours *LE 20 *AND *VALUE Local_Time.Day_Of_Week *NE Sunday *AND *VALUE Local_Time.Day_Of_Week *NE Saturday,

Situations open for long periods cause a steady drain on the TEMS and
the agent. This is especially true for situations which are deliberately
always true. The result can be a large TEMS process size and also situation
alerts which do not indicate a problem.

Recovery plan:  Review report and improve TEMS efficiency by eliminating
or redesigning the situation workloads.
----------------------------------------------------------------
