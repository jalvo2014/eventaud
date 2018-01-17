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
## identify multiple events at same time from sampled situations, missing atomize??

#use warnings::unused; # debug used to check for unused variables
use strict;
use warnings;

# See short history at end of module

my $gVersion = "1.03000";
my $gWin = (-e "C://") ? 1 : 0;    # 1=Windows, 0=Linux/Unix

use Data::Dumper;               # debug only

# a collection of variables which are used throughout the program.
# defined globally

my $args_start = join(" ",@ARGV);      # capture arguments for later processing
my $run_status = 0;                    # A count of pending runtime errors - used to allow multiple error detection before stopping process

# some common variables

my $rc;
my @words = ();
my $ll;
my $oneline;
my $sx;
my $f;
my $g;
my $h;

my %nodex;

my $event_min = 0;
my $event_max = 0;
my $event_dur = 0;

my %seq999;

my %seq998;


# forward declarations of subroutines

sub init;                                # read command line and ini file
sub logit;                               # queue one record to survey log
sub datadumperlog;                       # dump a variable using Dump::Data if installed
sub get_time;                             # get time
sub get_epoch;                            # get epoch from ITM stamp
sub init_all;                            # input from txt or lst files
sub newsit;                              # create new situation entry
sub newagt;                              # create new agemt entry
sub newlst;                              # create new TNODELST MSL entry
sub parse_lst;                           # parse the KfwSQLClient output
sub sec2time;

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
my @sit_psit = ();                         # array of printable situaton names
my @sit_sitinfo = ();                      # array of SITINFO columns
my @sit_autostart = ();                    # array of AUTOSTART columns
my @sit_sum = ();                          # count of *SUM
my @sit_agents = ();                       # Agents where this situation should run
my @sit_agenth = ();                       # hash of agent distribution
my @sit_cmd = ();                          # 1 if CMD is present
my @sit_dist = ();                         # When 1, distributed
my @sit_dist_objaccl = ();                 # Situation Distributions in TOBJACCL and TGROUP/TGROUPI
my @sit_process = ();                      # Process type attribute group
my @sit_reeval = ();                       # Sampling interval in seconds
my @sit_tfwd = ();                         # when 1, event forwarding enabled
my $sit_forwarded = 0;                     # when >0 some event forwarding is taking place

my @sit_statuscache = ();
my @sit_atomize = ();
my $sit_time_min = "";
my $sit_time_max =  "";
my $sit_total_statuscache = 0;

# option and ini file variables variables

my $opt_txt;                    # input from .txt files
my $opt_txt_tsitdesc;           # TSITDESC txt file
my $opt_txt_tsitstsh;           # TSITSTSH txt file
my $opt_txt_tname;              # TNAME txt file
my $opt_txt_tobjaccl;           # TOBJACCL txt file
my $opt_txt_tgroup;             # TGROUP txt file
my $opt_txt_tgroupi;            # TGROUPI txt file
my $opt_txt_tnodesav;           # TNODESAV txt file
my $opt_txt_tnodelst;           # TNODELST txt file
my $opt_lst;                    # input from .lst files
my $opt_lst_tsitdesc;           # TSITDESC lst file
my $opt_lst_tsitstsh;           # TSITDESH lst file
my $opt_lst_tname;              # TNAME lst file
my $opt_log;                    # name of log file
my $opt_ini;                    # name of ini file
my $opt_debuglevel;             # Debug level
my $opt_debug;                  # Debug level
my $opt_v;                      # verbose flag
my $opt_o;                      # output file
my $opt_odir;                   # Directory for output file
my $opt_workpath;               # Directory to store output files
my $opt_syntax;                 # syntax tracing
my $opt_all;                    # dump all details
my $opt_sum;                    # When 1 create summary file
my $opt_nohdr;                  # skip printing header

# produce output report
my @oline = ();
my $cnt = -1;

my $hdri = -1;                               # some header lines for report
my @hdr = ();                                #

# allow user to set impact
my %advcx = (
              "EVENTAUDIT1001W" => "75",
              "EVENTAUDIT1002E" => "100",
              "EVENTAUDIT1003W" => "80",
              "EVENTAUDIT1004W" => "75",
              "EVENTAUDIT1005W" => "70",
              "EVENTAUDIT1006W" => "70",
              "EVENTAUDIT1007W" => "80",
              "EVENTAUDIT1008E" => "100",
           );

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

$hdri++;$hdr[$hdri]="Situation Status History Audit Report $gVersion\n";
$hdri++;$hdr[$hdri] = "Runtime parameters: $arg_start";
$hdri++;$hdr[$hdri]="\n";

# process two different sources of situation event status data

$rc = init_all();

$event_dur = $event_max - $event_min;


my $outline;
foreach my $f (sort { $a cmp $b } keys %nodex ) {
   my $node_ref = $nodex{$f};
   foreach my $g (sort { $a cmp $b } keys %{$node_ref->{situations}} ) {
      my $situation_ref = $node_ref->{situations}{$g};
      my $sx = $sitx{$g};
      if (!defined $sx) {
         $advi++;$advonline[$advi] = "Situation Status on unknown situation $g on node $f";
         $advcode[$advi] = "EVENTAUDIT1001W";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = "TEMS";
      }
      foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{atomize}}) {
         my $atomize_ref = $situation_ref->{atomize}{$h};
         if ($h eq "") {
            if ($situation_ref->{reeval} != 0) {
               my $displayitem_prob = 1;
               foreach my $i (keys %{$atomize_ref->{secs}}) {
                  next if $atomize_ref->{secs}{$i} == 1;
                  $displayitem_prob = $atomize_ref->{secs}{$i};
                  last;
               }
               if ($displayitem_prob > 1) {
                  $advi++;$advonline[$advi] = "Situation $g on node $f showing $displayitem_prob events at same second - missing DisplayItem";
                  $advcode[$advi] = "EVENTAUDIT1002E";
                  $advimpact[$advi] = $advcx{$advcode[$advi]};
                  $advsit[$advi] = "TEMS";
               }
            }
         }
         my $detail_state = 1;   # wait for initial Y record
         my $detail_start;
         my $detail_end;
         my $detail_last = "";
         my $detail_ref;
         foreach my $i (sort {$atomize_ref->{details}{$a} cmp $atomize_ref->{details}{$b}} keys %{$atomize_ref->{details}}) {
            $detail_ref = $atomize_ref->{details}{$i};
            if ($situation_ref->{reeval} == 0) {
               $atomize_ref->{pure_ct} += 1;
               $situation_ref->{pure_ct} += 1;
            }
            # calculate open versus close for sampled events and thus calculate open time
            if ($situation_ref->{reeval} > 0) {
               if ($detail_state == 1) {   # waiting for Y record
                  if ($detail_ref->{deltastat} eq "Y") {
                     $detail_start = $detail_ref->{epoch};
                     $atomize_ref->{sampled_ct} += 1;
                     $situation_ref->{sampled_ct} += 1;
                     $situation_ref->{transitions} += 1;
                     $detail_state = 2;
                 } elsif ($detail_last eq "N") {
                     $detail_ref->{nn} += 1;          # record N followed by N
                     $atomize_ref->{nn} += 1;
                     $situation_ref->{nn} += 1;
                  }
               } elsif ($detail_state == 2) {    # waiting for N record
                  if ($detail_ref->{deltastat} eq "N") {
                     $detail_end = $detail_ref->{epoch};
                     $detail_ref->{open_time} += $detail_end - $detail_start;
                     $atomize_ref->{open_time} += $detail_end - $detail_start;
                     $situation_ref->{open_time} += $detail_end - $detail_start;
                     $situation_ref->{transitions} += 1;
                     $detail_state = 1;
                  } elsif ($detail_last eq "Y") {
                     $detail_ref->{yy} += 1;          # record Y followed by Y
                     $atomize_ref->{yy} += 1;
                     $situation_ref->{yy} += 1;
                  }
               }
               $detail_last = $detail_ref->{deltastat};
            }
         }
         if ($situation_ref->{reeval} > 0) {
            if ($detail_last eq "Y") {
               $atomize_ref->{open_time} += $event_max - $detail_start;
               $situation_ref->{open_time} += $event_max - $detail_start;
               $atomize_ref->{sampled_ct} = int($atomize_ref->{open_time}/$situation_ref->{reeval});
               $situation_ref->{sampled_ct} = int($situation_ref->{open_time}/$situation_ref->{reeval});
            }
         }
      }
   }
}

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
                                sampled_ct => 0,
                                pure_ct => 0,
                                close => 0,
                                atomize => {},
                                reeval => $situation_ref->{reeval},
                                transitions => 0,
                                tfwd => 0,
                                nodes => {},
                                nn => 0,
                                yy => 0,
                                time999 => {},
                                time998 => {},
                                ct999 => 0,
                                ct998 => 0,
                                node999 => {},
                                node998 => {},
                             );
          $situationx_ref = \%situationxref;
          $situationx{$g} = \%situationxref;
      }
      $situationx_ref->{count} += $situation_ref->{count};
      $situationx_ref->{open} += $situation_ref->{open};
      $situationx_ref->{close} += $situation_ref->{close};
      $situationx_ref->{bad} += $situation_ref->{bad};
      $situationx_ref->{sampled_ct} += $situation_ref->{sampled_ct};
      $situationx_ref->{pure_ct} += $situation_ref->{pure_ct};
      $situationx_ref->{nn} += $situation_ref->{nn};
      $situationx_ref->{yy} += $situation_ref->{yy};
      $situationx_ref->{transitions} += $situation_ref->{transitions};
      $situationx_ref->{tfwd} = $situation_ref->{tfwd};
      $situationx_ref->{nodes}{$f} += 1;
      foreach my $h (keys %{$situation_ref->{atomize}}) {
         $situationx_ref->{atomize}{$h} += 1;
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

my $total_count = 0;
my $total_open = 0;
my $total_close = 0;
my $total_sampled = 0;
my $total_pure = 0;
my $total_transitions = 0;
my $total_yy = 0;
my $total_nn = 0;
my $res_rate;
my $ppc;

foreach $g (keys %situationx) {
   my $situationx_ref = $situationx{$g};
   $total_count += $situationx_ref->{count};
   $total_open += $situationx_ref->{open};
   $total_close += $situationx_ref->{close};
   $total_sampled += $situationx_ref->{sampled_ct};
   $total_pure += $situationx_ref->{pure_ct};
   $total_transitions += $situationx_ref->{transitions};
   $total_yy += $situationx_ref->{yy};
   $total_nn += $situationx_ref->{nn};
}

$rptkey = "EVENTREPORT000";$advrptx{$rptkey} = 1;         # record report key
$hdri++;$hdr[$hdri]="$rptkey: Summary report";
$hdri++;$hdr[$hdri]="Duration $event_dur seconds";
$res_rate = 0;
$res_rate = ($total_count*60)/$event_dur if $event_dur > 0;
$ppc = sprintf '%.2f', $res_rate;
$hdri++;$hdr[$hdri]="Event Status History count $total_count $ppc/min";

my $ppc_event_rate = $ppc;

$res_rate = 0;
$res_rate = ($total_open*60)/$event_dur if $event_dur > 0;
$ppc = sprintf '%.2f', $res_rate;
$hdri++;$hdr[$hdri]="Event Status History open $total_open $ppc/min";

$res_rate = 0;
$res_rate = ($total_close*60)/$event_dur if $event_dur > 0;
$ppc = sprintf '%.2f', $res_rate;
$hdri++;$hdr[$hdri]="Event Status History close $total_close $ppc/min";

$res_rate = 0;
$res_rate = ($total_transitions*60)/$event_dur if $event_dur > 0;
$ppc = sprintf '%.2f', $res_rate;
$hdri++;$hdr[$hdri]="Event Status History transitions $total_transitions $ppc/min";
$hdri++;$hdr[$hdri]="Event Status History Open->Open transitions $total_yy";
$hdri++;$hdr[$hdri]="Event Status History Close->Close transitions $total_nn";

$res_rate = 0;
$res_rate = ($total_sampled*60)/$event_dur if $event_dur > 0;
$ppc = sprintf '%.2f', $res_rate;
$hdri++;$hdr[$hdri]="Event Result History sampled $total_sampled $ppc/min";

my $ppc_sample_rate = $ppc;

$res_rate = 0;
$res_rate = ($total_pure*60)/$event_dur if $event_dur > 0;
$ppc = sprintf '%.2f', $res_rate;
$hdri++;$hdr[$hdri]="Event Result History pure $total_pure $ppc/min";


$rptkey = "EVENTREPORT001";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$outline = "$rptkey: Event Summary sorted by Event Status Count";
$cnt++;$oline[$cnt]="$outline\n";
$outline = "Situation,Count,Count%,Count/min,Open,Close,Sampled,Sampled%,Sampled/min,Pure,Pure%,Pure/min,Atomize,Nodes,Transitions,Tr/hour,PDT";
$cnt++;$oline[$cnt]="$outline\n";
my $res_pc;
foreach $g ( sort { $situationx{$b}->{count} <=>  $situationx{$a}->{count} }  keys %situationx) {
   my $situationx_ref = $situationx{$g};
   $outline = $g . ",";
   $outline .= $situationx_ref->{count} . ",";
   $res_pc = ($situationx_ref->{open}*100)/$total_count;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $res_rate = 0;
   $res_rate = ($situationx_ref->{count}*60)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   $outline .= $situationx_ref->{open} . ",";
   $outline .= $situationx_ref->{close} . ",";
   $outline .= $situationx_ref->{sampled_ct} . ",";
   $ppc = "0.00%";
   if ($total_sampled > 0) {
      $res_pc = ($situationx_ref->{sampled_ct}*100)/$total_sampled;
      $ppc = sprintf '%.2f%%', $res_pc;
   }
   $outline .= $ppc . ",";
   $res_rate = 0;
   $res_rate = ($situationx_ref->{sampled_ct}*60)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   $outline .= $situationx_ref->{pure_ct} . ",";
   $ppc = "0.00%";
   if ($total_pure > 0) {
      $res_pc = ($situationx_ref->{pure_ct}*100)/$total_pure;
      $ppc = sprintf '%.2f%%', $res_pc;
   }
   $outline .= $ppc . ",";
   $res_rate = 0;
   $res_rate = ($situationx_ref->{pure_ct}*60)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   my $ct = scalar keys %{$situationx_ref->{atomize}};
   $outline .= $ct . ",";
   my $node_ct = scalar keys %{$situationx_ref->{nodes}};
   $outline .= $node_ct . ",";
   $outline .= $situationx_ref->{transitions} . ",";
   $res_rate = 0;
   $res_rate = ($situationx_ref->{transitions}*3600)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   my $ppdt = "";
   my $sx = $sitx{$g};
   $ppdt = $sit_pdt[$sx] if defined $sx;
   $outline .= $ppdt . ",";
   $cnt++;$oline[$cnt]="$outline\n";
   $res_rate = ($situationx_ref->{transitions}*3600)/($event_dur*$node_ct) if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   if ($res_rate >= 1) {
      $advi++;$advonline[$advi] = "Situation $g on showing $ppc open<->close transitions per hour per agent over $node_ct agents";
      $advcode[$advi] = "EVENTAUDIT1003W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = "TEMS";
   }
   if ($situationx_ref->{tfwd} == 0) {   # is this event forwarded
      if ($sit_forwarded > 0) {          # are any events forwarded
         $advi++;$advonline[$advi] = "Situation $g showing $situationx_ref->{count} event statuses over $node_ct agents - but event not forwarded";
         $advcode[$advi] = "EVENTAUDIT1004W";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = "TEMS";
      }
   }
   if ($situationx_ref->{yy} > 0) {
      $advi++;$advonline[$advi] = "Situation $g showing $situationx_ref->{yy} open->open transitions over $node_ct agents";
      $advcode[$advi] = "EVENTAUDIT1005W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = "TEMS";
   }
   if ($situationx_ref->{nn} > 0) {
      $advi++;$advonline[$advi] = "Situation $g showing $situationx_ref->{nn} close->close transitions over $node_ct agents";
      $advcode[$advi] = "EVENTAUDIT1006W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = "TEMS";
   }
}

$rptkey = "EVENTREPORT002";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$outline = "$rptkey: Event Summary sorted by Event Status Samples";
$cnt++;$oline[$cnt]="$outline\n";
$outline = "Situation,Count,Count%,Count/min,Open,Close,Sampled,Sampled%,Sampled/min,Pure,Pure%,Pure/min,Atomize,Nodes,Transitions,Tr/hour,PDT";
$cnt++;$oline[$cnt]="$outline\n";
foreach $g ( sort { $situationx{$b}->{sampled_ct} <=>  $situationx{$a}->{sampled_ct} }  keys %situationx) {
   my $situationx_ref = $situationx{$g};
   $outline = $g . ",";
   $outline .= $situationx_ref->{count} . ",";
   $res_pc = ($situationx_ref->{open}*100)/$total_count;
   $ppc = sprintf '%.2f%%', $res_pc;
   $outline .= $ppc . ",";
   $res_rate = 0;
   $res_rate = ($situationx_ref->{count}*60)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   $outline .= $situationx_ref->{open} . ",";
   $outline .= $situationx_ref->{close} . ",";
   $outline .= $situationx_ref->{sampled_ct} . ",";
   $ppc = "0.00%";
   if ($total_sampled > 0) {
      $res_pc = ($situationx_ref->{sampled_ct}*100)/$total_sampled;
      $ppc = sprintf '%.2f%%', $res_pc;
   }
   $outline .= $ppc . ",";
   $res_rate = 0;
   $res_rate = ($situationx_ref->{sampled_ct}*60)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   $outline .= $situationx_ref->{pure_ct} . ",";
   $ppc = "0.00%";
   if ($total_pure > 0) {
      $res_pc = ($situationx_ref->{pure_ct}*100)/$total_pure;
      $ppc = sprintf '%.2f%%', $res_pc;
   }
   $outline .= $ppc . ",";
   $res_rate = 0;
   $res_rate = ($situationx_ref->{pure_ct}*60)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   my $ct = scalar keys %{$situationx_ref->{atomize}};
   $outline .= $ct . ",";
   $ct = scalar keys %{$situationx_ref->{nodes}};
   $outline .= $ct . ",";
   $outline .= $situationx_ref->{transitions} . ",";
   $res_rate = 0;
   $res_rate = ($situationx_ref->{transitions}*3600)/$event_dur if $event_dur > 0;
   $ppc = sprintf '%.2f', $res_rate;
   $outline .= $ppc . ",";
   my $ppdt = "";
   my $sx = $sitx{$g};
   $ppdt = $sit_pdt[$sx] if defined $sx;
   $outline .= $ppdt . ",";
   $cnt++;$oline[$cnt]="$outline\n";
}

my $node999_total = 0;
my $time999_total = 0;

$rptkey = "EVENTREPORT004";$advrptx{$rptkey} = 1;         # record report key
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
   foreach my $i (sort {$situation_ref->{time999}{$b} <=> $situation_ref->{time999}{$a}} keys %{$situation_ref->{time999}}) {
      $tp .= $i . "[" . $situation_ref->{time999}{$i} . "] ";
      $time999_total += $situation_ref->{time999}{$i};
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

$rptkey = "EVENTREPORT005";$advrptx{$rptkey} = 1;         # record report key
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
   foreach my $i (sort {$situation_ref->{time998}{$b} <=> $situation_ref->{time998}{$a}} keys %{$situation_ref->{time998}}) {
      $tp .= $i . "[" . $situation_ref->{time998}{$i} . "] ";
   }
   $outline .= $tp . ",";
   $cnt++;$oline[$cnt]="$outline\n";
}

$rptkey = "EVENTREPORT006";$advrptx{$rptkey} = 1;         # record report key
$cnt++;$oline[$cnt]="\n";
$outline = "$rptkey: Deltastat X report";
$cnt++;$oline[$cnt]="$outline\n";
$outline = "Situation,Count,";
$cnt++;$oline[$cnt]="$outline\n";
my $bad_ct = 0;
my $bad_total = 0;
foreach $g ( sort { $situationx{$b}->{ct998} <=> $situationx{$a}->{ct998}}  keys %situationx) {
   my $situation_ref = $situationx{$g};
   next if $situation_ref->{bad} == 0;
   $bad_ct += 1;
   $bad_total +=  $situation_ref->{bad};
   $outline = $g . ",";
   $outline .= $situation_ref->{bad} . ",";
   $cnt++;$oline[$cnt]="$outline\n";
}
if ($bad_ct > 0) {
   $advi++;$advonline[$advi] = "Situations [$bad_ct] had lodge failures [$bad_total] - See report $rptkey";
   $advcode[$advi] = "EVENTAUDIT1008E";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "TEMS";
}

if ($opt_all == 1) {
   $rptkey = "EVENTREPORT003";$advrptx{$rptkey} = 1;         # record report key
   $cnt++;$oline[$cnt]="\n";
   $outline = "$rptkey: Full report sorted by Node/Situation/Time";
   $cnt++;$oline[$cnt]="Node,Situation,Time,Deltastat,Reeval,Atomize,\n";
   foreach my $f (sort { $a cmp $b } keys %nodex ) {
      my $node_ref = $nodex{$f};
      foreach my $g (sort { $a cmp $b } keys %{$node_ref->{situations}} ) {
         my $situation_ref = $node_ref->{situations}{$g};
         foreach my $h ( sort {$a cmp $b} keys %{$situation_ref->{atomize}}) {
         my $atomize_ref = $situation_ref->{atomize}{$h};
            foreach my $i (sort {$atomize_ref->{details}{$a} cmp $atomize_ref->{details}{$b}} keys %{$atomize_ref->{details}}) {
               my $detail_ref = $atomize_ref->{details}{$i};
               $outline = $f . "," . $g . "," . $detail_ref->{time} . "," . $detail_ref->{deltastat} . "," . $situation_ref->{reeval} . "," . $h . ",";
               $cnt++;$oline[$cnt]="$outline\n";
            }
         }
      }
   }
}

$opt_o = $opt_odir . $opt_o if index($opt_o,'/') == -1;

open OH, ">$opt_o" or die "unable to open $opt_o: $!";

if ($opt_nohdr == 0) {
   for (my $i=0; $i<=$hdri; $i++) {
      print OH $hdr[$i] . "\n";
   }
   print OH "\n";
}

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

for (my $i = 0; $i<=$cnt; $i++) {
   print OH $oline[$i];
}

if ($advi != -1) {
   print OH "\n";
   print OH "Event History Advisory Messages, Meaning and Recovery suggestions follow\n\n";
   foreach $f ( sort { $a cmp $b } keys %advgotx ) {
      next if substr($f,0,10) ne "EVENTAUDIT";
      print OH "Advisory code: " . $f  . "\n";
      print OH "Impact:" . $advgotx{$f}  . "\n";
#     print STDERR "$f missing\n" if !defined $advtextx{$f};
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

if ($opt_sum != 0) {
   my $sumline;
# EVENTAUD 100 25
   $sumline = "EVENTAUDIT ";
   my $padvi = $advi + 1;
   $sumline .= $max_impact . " ";
   $sumline .= $padvi . " ";
   $sumline .= $event_dur . " seconds ";
   $sumline .= $total_count . " events" . "[$ppc_event_rate/min] ";
   $sumline .= $total_sampled . " results" . "[$ppc_sample_rate/min] ";
   my $sumfn = $opt_odir . "eventaud.txt";
   open SUM, ">$sumfn" or die "Unable to open summary file $sumfn\n";
   print SUM "$sumline\n";
   close(SUM);
}

exit;

sub newnam {
      my ($iid,$ifullname) = @_;
      $sitfullx{$iid} = $ifullname;
}
sub newsit {
      my ($isitname,$isitinfo,$ireev_days,$ireev_time,$ipdt) = @_;
      $siti += 1;
      $sit[$siti] = $isitname;
      $sitx{$isitname} = $siti;
      $sit_sitinfo[$siti] = $isitinfo;
      $sit_statuscache[$siti] = 0;
      $sit_atomize[$siti] = 0;
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
}
sub newstsh {
   my ($ill,$isitname,$ideltastat,$ioriginnode,$ilcltmstmp,$inode,$iatomize) = @_;

   my $node_ref = $nodex{$ioriginnode};

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
   $node_ref->{close} += 1 if $ideltastat eq "N";
   $node_ref->{thrunodes}{$inode} += 1;
   my $situation_ref = $node_ref->{situations}{$isitname};
   if (!defined $situation_ref) {
      my %situationref = (
                            count => 0,
                            open => 0,
                            sampled_ct => 0,
                            pure_ct => 0,
                            close => 0,
                            bad => 0,
                            open_time => 0,
                            atomize => {},
                            reeval => 0,
                            transitions => 0,
                            tfwd => 0,
                            nn => 0,
                            yy => 0,
                            time999 => {},
                            time998 => {},
                            node999 => {},
                            node998 => {},
                         );
      $situation_ref = \%situationref;
      $node_ref->{situations}{$isitname} = \%situationref;
      my $sx = $sitx{$isitname};
      $situation_ref->{reeval} = $sit_reeval[$sx] if defined $sx;
      $situation_ref->{tfwd} = $sit_tfwd[$sx] if defined $sx;
   }
   $situation_ref->{count} += 1;
   $situation_ref->{open} += 1 if $ideltastat eq "Y";
   $situation_ref->{close} += 1 if $ideltastat eq "N";
   $situation_ref->{bad} += 1 if $ideltastat eq "X";
   my $atomize_ref = $situation_ref->{atomize}{$iatomize};
   if (!defined $atomize_ref) {
      my %atomizeref = (
                          count => 0,
                          open => 0,
                          close => 0,
                          bad => 0,
                          open_time => 0,
                          sampled_ct => 0,
                          pure_ct => 0,
                          details => {},
                          time_min => "",
                          time_max => "",
                          reeval => 0,
                          secs => {},
                          nn => 0,
                          yy => 0,
                       );
      $atomize_ref = \%atomizeref;
      $situation_ref->{atomize}{$iatomize} = \%atomizeref;
   }
   if ($atomize_ref->{time_min} eq "") {
      $atomize_ref->{time_min} = $ilcltmstmp;
      $atomize_ref->{time_max} = $ilcltmstmp;
   }
   $atomize_ref->{time_min} = $ilcltmstmp if $ilcltmstmp lt $atomize_ref->{time_min};
   $atomize_ref->{time_max} = $ilcltmstmp if $ilcltmstmp gt $atomize_ref->{time_max};
   $atomize_ref->{count} += 1;
   $atomize_ref->{open} += 1 if $ideltastat eq "Y";
   $atomize_ref->{close} += 1 if $ideltastat eq "N";
   $atomize_ref->{bad} += 1 if $ideltastat eq "X";

   my %event_details = (
                          time => $ilcltmstmp,
                          epoch => 0,
                          deltastat => $ideltastat,
                          open_time => 0,
                          sampled_ct => 0,
                          pure_ct => 0,
                          nn => 0,
                          yy => 0,
                       );
   $event_details{epoch} = get_epoch($ilcltmstmp);
   $atomize_ref->{secs}{$event_details{epoch}} += 1;
   $atomize_ref->{details}{$ill} = \%event_details;
   if (substr($ilcltmstmp,-3,3) eq "999") {
      $situation_ref->{time999}{$ilcltmstmp} += 1;
      $situation_ref->{node999}{$ioriginnode} += 1;
   } elsif (substr($ilcltmstmp,-3,3) eq "998") {
      $situation_ref->{time998}{$ilcltmstmp} += 1;
      $situation_ref->{node998}{$ioriginnode} += 1;
   }

   # track global start/stop time
   if ($event_min == 0) {
      $event_min = $event_details{epoch};
      $event_max = $event_details{epoch};
   }
   $event_min = $event_details{epoch} if $event_details{epoch} < $event_min;
   $event_max = $event_details{epoch} if $event_details{epoch} > $event_max;
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
   my $inode;
   my $iatomize;

   my $read_fn;

   # (1) the TNAME data
   if ($opt_txt == 1) {
      $read_fn = $opt_txt_tname;
      $read_fn = $opt_workpath . $opt_txt_tname if -e $opt_workpath . $opt_txt_tname;
   } else {
      $read_fn = $opt_lst_tname;
      $read_fn = $opt_workpath . $opt_lst_tname if -e $opt_workpath . $opt_lst_tname;
   }
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
   open(KSTSH, "< $read_fn") || die("Could not open TSITSTSH $read_fn\n");
   @kstsh_data = <KSTSH>;
   close(KSTSH);

   $ll = 0;
   foreach $oneline (@kstsh_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $oneline .= " " x 200;
      if ($opt_txt == 1) {
         $isitname = substr($oneline,0,32);
         $isitname =~ s/\s+$//;   #trim trailing whitespace
         $ideltastat = substr($oneline,33,1);
         $ideltastat =~ s/\s+$//;   #trim trailing whitespace
         $ioriginnode = substr($oneline,43,32);
         $ioriginnode =~ s/\s+$//;   #trim trailing whitespace
         $ilcltmstmp = substr($oneline,76,16);
         $ilcltmstmp =~ s/\s+$//;   #trim trailing whitespace
         $inode = substr($oneline,93,32);
         $inode =~ s/\s+$//;   #trim trailing whitespace
         $iatomize = substr($oneline,126,128);
         $iatomize =~ s/\s+$//;   #trim trailing whitespace
      } else {
         next if substr($oneline,0,1) ne "[";                    # Look for starting point
         ($isitname,$ideltastat,$ioriginnode,$ilcltmstmp,$inode,$iatomize) = parse_lst(6,$oneline);
         $isitname =~ s/\s+$//;   #trim trailing whitespace
         $ideltastat =~ s/\s+$//;   #trim trailing whitespace
         $ioriginnode =~ s/\s+$//;   #trim trailing whitespace
         $ilcltmstmp =~ s/\s+$//;   #trim trailing whitespace
         $inode =~ s/\s+$//;   #trim trailing whitespace
         $iatomize =~ s/\s+$//;   #trim trailing whitespace
      }
      next if ($ideltastat ne 'Y') and ($ideltastat ne 'N') and ($ideltastat ne 'X');
      newstsh($ll,$isitname,$ideltastat,$ioriginnode,$ilcltmstmp,$inode,$iatomize);
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
      } elsif ($ARGV[0] eq "-all") {
         $opt_all = 1;
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
      } elsif ($ARGV[0] eq "-odir") {
         shift(@ARGV);
         $opt_odir = shift(@ARGV);
         die "odir specified but no path found\n" if !defined $opt_odir;
      } elsif ($ARGV[0] eq "-workpath") {
         shift(@ARGV);
         $opt_workpath = shift(@ARGV);
         die "workpath specified but no path found\n" if !defined $opt_workpath;
      }
      else {
         $logfn = shift(@ARGV);
         die "log file not defined\n" if !defined $logfn;
      }
   }

   if (!defined $logfn) {$logfn = "";}
   if (!defined $opt_v) {$opt_v = 0;}
   if (!defined $opt_nohdr) {$opt_nohdr = 0;}
   if (!defined $opt_o) {$opt_o = "eventaud.csv";}
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
   if (!defined $opt_all) {$opt_all=1;}                       # initial testing show all details
   if (defined $opt_txt) {
      $opt_txt_tsitdesc = "QA1CSITF.DB.TXT";
      $opt_txt_tsitstsh = "QA1CSTSH.DB.TXT";
      $opt_txt_tname = "QA1DNAME.DB.TXT";
   }
   if (defined $opt_lst) {
      $opt_lst_tsitdesc = "QA1CSITF.DB.LST";
      $opt_lst_tsitstsh = "QA1CSTSH.DB.LST";
      $opt_lst_tname = "QA1DNAME.DB.LST";
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
      $unixtime = mktime ($iss, $imm, $ihh, $idd, $imo, $iyy, $wday, $yday);
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
# Following is the embedded "DATA" file used to explain
# advisories and reports.
__END__

EVENTAUDIT1001W
Text: Situation Status on unknown situation <situation> on node <agent>

Meaning: There are rare cases where situations keep running
at an agent even though the situation was deleted. This causes
excessive work.

Recovery plan: If the TEMS and TEMA [Agent Support Library] are
at maintenance level ITM 630 FP2 or higher, recyle the agent
and the condition will be resolved. Otherwise contact IBM Support
for assistance.
--------------------------------------------------------------

EVENTAUDIT1002E
Text: Situation <situation> on node <agent> showing <count> events at same second - missing DisplayItem

Meaning: The agent is returning multiple events for this situation.
Because of the missing DisplayItem setting, only a single event
will be created. This causes poor monitoring since some events
are not created.

Recovery plan: Add DisplayItem to the situation.
--------------------------------------------------------------

EVENTAUDIT1003W
Text: Situation <situation> on showing <rate> open<->close transitions per hour over <count> agents

Meaning: A situation that shows a lot of transitions from open [Y]
to closed [N] and many times is not good. Best situations show go
open and stay open until the condition is closed and then stay closed.

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
Text: Situation <situation> showing <count> event statuses over <count> agents - but event not forwarded

Meaning: The situation is creating a lot of situation event statuses.
However the event is not forwarded to an event receiver. This may be
normal if no event receiver is used. However if there is an event
receiver like Netcool/Omnibus, this could be a hidden drag on ITM
processing that is hurting performance with no benefit.

Recovery plan: Review these such situations and see if they are still
needed. If not, stop them and probably delete them.
--------------------------------------------------------------

EVENTAUDIT1005W
Text: Situation <situation> showing <count> open->open transitions over <count> agents

Meaning: Normal transitions are open->close->open. Some causes:
1) Missing DisplayItem
2) Duplicate Agent name cases
3) Agent recycled after a crash.

Recovery plan: Review these such cases and resolve any issues.
--------------------------------------------------------------

EVENTAUDIT1006W
Text: Situation <situation> showing <count> close->close transitions over <count> agents

Meaning: Normal transitions are open->close->open. Some causes:
1) Overloaded agent. An agent that does not not repeat results
after 3 sampling intervals will have situation auto-closed by TEMS.
2) Duplicate Agent name cases
3) Agent recycled after a crash.

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

Meaning: Some situation could not be started cause they
had a severe error such as an unknown attribute or a
test value that exceeded the allowed length.

See related report EVENTREPORT0076 for more details.

Recovery plan: Correct the situations. Also review the
agent development process to make sure they are tested.
--------------------------------------------------------------

EVENTREPORT000
Text: Summary lines

Sample:
to be added later

Meaning: One quick note, if negative numbers are seen, there
are likely a lot of event status seen with the same time stamp.

Recovery plan:  Use for a quick summary of condition.
----------------------------------------------------------------

EVENTREPORT001
Text: Event Summary sorted by Event Status Count

Sample:
Event Summary sorted by Event Status Samples
Situation,Count,Count%,Count/min,Open,Close,Sampled,Sampled%,Sampled/min,Pure,Pure%,Pure/min,Atomize,Nodes,Transitions,Tr/hour,PDT
bnc_hakapps_xvaw_viosgr,48,1.09%,0.11,41,7,14008,15.67%,33.08,0,0.00%,0.00,6,32,44,6.24,
bnc_adskprc_xvaw_viosgr,146,2.00%,0.34,75,71,8686,9.72%,20.51,0,0.00%,0.00,43,9,95,13.46,

Meaning: Report what situation created the most situation results

Sorted in reverse number by the number of event results observed. This report
is different from EVENTREPORT001 by estimating incoming results. A single
situation open event will result in multiple results since the agent periodically
resends result rows in order to "confirm" the condition is still true.

Situation    : Situation Name. This can be the name index in case TNAME Fullname is used
Count        : Number of situation status events
Count%       : Per Cent of total situation status events
Count/min    : Rate per minute of situation status events
Open         : Number of Open events
Close        : Number of Close events
Sampled      : Number of sampled situation events
Sampled%     : Per Cent of sampled situation events
Sampled/min  : Rare of sampled situation events
Pure         : Number of pure situation events
Pure%        : Per Cent of pure situation events
Pure/min     : Rate of pure situation events
Atomize      : Number of different Atomize values
Nodes        : Number of reporting nodes [agents]
Transitions  : Transitions from one open/close to another
Tr/hour      : Rate of transitions per hour
PDT          : Situation Formula [predicate]

There are savings to be had be reducing the number of situations event statuses.
The benefit is both at the remote TEMS and the hub TEMS.

Recovery plan:  Review report and improve TEMS efficiency by eliminating
or redesigning the situation workloads.
----------------------------------------------------------------

EVENTREPORT002
Text: Event Summary sorted by Event Status Samples

Sample:
Event Summary sorted by Event Status Count
Situation,Count,Count%,Count/min,Open,Close,Sampled,Sampled%,Sampled/min,Pure,Pure%,Pure/min,Atomize,Nodes,Transitions,Tr/hour
bnc_svrdsfr_gvmm_vmvigr,576,10.25%,1.36,384,192,3381,3.78%,7.99,0,0.00%,0.00,65,54,399,56.54,
bnc_undosp_grzm_oraclev10gr,557,14.66%,1.32,549,8,2696,3.02%,6.37,0,0.00%,0.00,1,35,47,6.66,


Meaning: Report what situation created the most situation event statuses.

Sorted in reverse number by the number of event status observed. This report
only counts Open [Y] and Close [Y] status and ignores others such as Start [S]
and Stop [S] because those are not associated with specific agents.


Situation,Count,Count%,Count/min,Open,Close,Sampled,Sampled%,Sampled/min,Pure,Pure%,Pure/min,Atomize,Nodes,Transitions,Tr/hour,PDT

Situation    : Situation Name. This can be the name index in case TNAME Fullname is used
Count        : Number of situation results
Count%       : Per Cent of total situation results
Count/min    : Rate per minute of situation results
Open         : Number of Open events
Close        : Number of Close events
Sampled      : Number of sampled results
Sampled%     : Per Cent of sampled results
Sampled/min  : Rare of sampled results
Pure         : Number of pure results
Pure%        : Per Cent of pure results
Pure/min     : Rate of pure result
Atomize      : Number of different Atomize values
Nodes        : Number of reporting nodes [agents]
Transitions  : Transitions from one open/close to another
Tr/hour      : Rate of transitions per hour
PDT          : Situation Formula [predicate]

There are major savings to be had be reducing the number of incoming
situation results at a remote TEMS. The benefit is mostly at the
TEMS receiving results, usually the remote TEMS.

Recovery plan:  Review report and improve TEMS efficiency by eliminating
or redesigning the situation workloads.
----------------------------------------------------------------

EVENTREPORT003
Text: Full report sorted by Node/Situation/Time

Sample:
Node,Situation,Reeval,Time,Deltastat,Atomize,
BN:BNCSP-03VA-DATAPW01b:DPS,bnc_noresponse_gbnp_datapower,1171210023655998,Y,120,,
BN:BNCSP-03VA-DATAPW01b:DPS,bnc_noresponse_gbnp_datapower,1171210023655001,Y,120,,

Meaning: Report what situation created the most situation event statuses.

Sorted in Node then Situation then Time order. This section can be used to
understand exactly what conditions were observed.


Situation,Count,Count%,Count/min,Open,Close,Sampled,Sampled%,Sampled/min,Pure,Pure%,Pure/min,Atomize,Nodes,Transitions,Tr/hour

Node         : Agent name
Situation    : Situation Name. This can be the name index in case TNAME Fullname is used
Time         : Time when situation status was observed in ITM time format CYYMMDDHHMMSSXXX
Deltastat    : Y for Open and N for Close
Reeval       : Situation Samplinging interval - zero means a pure situation
Atomize      : Value of atomize if any for this

This report is mainly to help understand the summary reports.

Recovery plan:  Use report to help understand the summary reports.
----------------------------------------------------------------

EVENTREPORT004
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

EVENTREPORT005
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

EVENTREPORT006
Text: Deltastat X report

Sample:
Situation,Count,Nodes,Times
ddb_fss_xuxc_ws,3,

Meaning: This Situation had some serious error can could not run.
TEMS assigns a status of X and does not run it.

Recovery plan: Correct the situaton so it works. The diagnostic log
will contain details about the error.
----------------------------------------------------------------
