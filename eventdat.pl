#!/usr/local/bin/perl -w
#------------------------------------------------------------------------------
# Licensed Materials - Property of IBM (C) Copyright IBM Corp. 2010, 2010
# All Rights Reserved US Government Users Restricted Rights - Use, duplication
# or disclosure restricted by GSA ADP Schedule Contract with IBM Corp
#------------------------------------------------------------------------------

#  perl inodests_sum.pl
#
#  Identify possible duplicate agent name cases
#
#  john alvord, IBM Corporation, 15 March 2016
#  jalvord@us.ibm.com
#
# tested on Windows Activestate 5.20.2
# Should work on Linux/Unix but not yet tested
#
#    # remember debug breakpoint
# $DB::single=2;   # remember debug breakpoint

#use warnings::unused; # debug used to check for unused variables
use strict;
use warnings;
use Cwd;
my $cwd = getcwd;

# See short history at end of module

my $gVersion = "0.56000";
my $gWin = (-e "C://") ? 1 : 0;    # 1=Windows, 0=Linux/Unix

use Data::Dumper;               # debug only

sub get_inodests;

my %node_status;

my %host_addrx;

my $nsavei = -1;
my $nsx;
my @nsave;
my %nsavex;
my @nsave_expirytime;
my @nsave_gbltmstmp;
my @nsave_hostaddr;
my @nsave_hostinfo;
my @nsave_o4online;
my @nsave_product;
my @nsave_reserved;
my @nsave_thrunode;
my @nsave_version;
my @nsave_affinities;

my %wtems;
my $wtemsi = 0;

my $temsi = -1;
my @tems;
my %temsx;
my @tems_ishub;
my $tems_hub;
my $total_agents = 0;

my $cmd;
my $rc;
my $sSQL;
my $sAT;
my $install;
my $ksc;
my $ksc_base;
my $ptemp;
my $sqlfile;
my $lstfile;
my $ll;
my $oneline;
my $delim;

my $opt_all;
my $opt_aff;
my $opt_v;
my $opt_redo;
my $opt_off;
my $opt_thrunode;
my $opt_home;
my $opt_o;
my $opt_work;

while (@ARGV) {
   if ($ARGV[0] eq "-all") {
      shift(@ARGV);
      $opt_all = 1;
   } elsif ($ARGV[0] eq "-aff") {
      shift(@ARGV);
      $opt_aff = 1;
   } elsif ($ARGV[0] eq "-v") {
      shift(@ARGV);
      $opt_v = 1;
   } elsif ($ARGV[0] eq "-off") {
      shift(@ARGV);
      $opt_off = 1;
   } elsif ($ARGV[0] eq "-thrunode") {
      shift(@ARGV);
      $opt_thrunode = 1;
   } elsif ($ARGV[0] eq "-redo") {
      shift(@ARGV);
      $opt_redo = 1;
   } elsif ($ARGV[0] eq "-h") {
      shift(@ARGV);
      $opt_home = shift(@ARGV);
      die if !defined $opt_home;
   } elsif ($ARGV[0] eq "-tems") {
      shift(@ARGV);
      my $wanted = shift(@ARGV);
      die "-tems supplied with no tems nodeid" if !defined $wanted;
      $wtems{$wanted} = 1;
   } elsif ($ARGV[0] eq "-o") {
      shift(@ARGV);
      $opt_o = shift(@ARGV);
      die if !defined $opt_o;
   } elsif ($ARGV[0] eq "-work") {
      shift(@ARGV);
      $opt_work = shift(@ARGV);
      die if !defined $opt_work;
   }
}

$opt_all = 0 if !defined $opt_all;
$opt_redo = 0 if !defined $opt_redo;
$opt_aff = 0 if !defined $opt_aff;
$opt_v = 0 if !defined $opt_v;
$opt_off = 0 if !defined $opt_off;
$opt_thrunode = 0 if !defined $opt_thrunode;
$opt_o = "inodests_sum.csv" if !defined $opt_o;
if (!defined $opt_work) {
   if ($gWin == 1) {
      $opt_work = 'c:\temp';
   } else {
     $opt_work = '/tmp';
   }
}
$opt_work = $cwd if $opt_work eq ".";

$wtemsi = scalar keys %wtems;

if (!defined $opt_home) {
   if ($gWin == 1) {
      $opt_home = $ENV{'CANDLE_HOME'};
      $opt_home = 'C:\IBM\ITM' if !defined $opt_home;
   } else {
      $opt_home = $ENV{'CANDLEHOME'};
      $opt_home = '/opt/IBM/ITM' if !defined $opt_home;
   }
}


if ($gWin == 1) {
  # KfwSQLClient /v /f c:\temp\test.sql  >c:\temp\test.lst
 $ksc_base = $opt_home . '\cnps\KfwSQLClient /v /f ' . $opt_work . '\inodests.sql > ';
  $delim = "\\";
} else {
  # /opt/IBM/ITM/bin/itmcmd execute cq "KfwSQLClient /v /f /tmp/itcamyn.sql"
 $ksc_base = $opt_home . '/bin/itmcmd execute cq "KfwSQLClient /f ' . $opt_work . '/eventaud.sql" > ';
  $delim = "/";
}

$sqlfile = $opt_work . $delim . "inodests.sql";

# gather INODESTS from hub TEMS - to calculate the TEMSes in the environment

$sSQL ="SELECT EXPIRYTIME,GBLTMSTMP,HOSTADDR,HOSTINFO,NODE,O4ONLINE,PRODUCT,RESERVED,THRUNODE,VERSION,AFFINITIES FROM O4SRV.INODESTS";

# Run KfwSQLClient to get and process the data. Result is stored in the @nsave_ arrays.
get_inodests($sSQL);
print STDERR "Got INODESTS from hub TEMS\n" if $opt_v == 1;

# pass one: figure out which is hub TEMS
for (my $i=0;$i<=$nsavei;$i++) {
   next if $nsave_o4online[$i] ne "Y";          # ignore unless online
   next if $nsave[$i] ne $nsave_thrunode[$i];   # ignore unless it is its own thrunode
   $tems_hub = $nsave[$i];                      # save away as the Hub TEMS nodeid
   $temsi += 1;                                 # add hub TEMS as first entry in tems array
   $tems[$temsi] = $nsave[$i];
   $tems_ishub[$temsi] = 1;
   $temsx{$nsave[$i]} = $temsi;
   last;
}
print STDERR "Hub TEMS is $tems_hub\n" if $opt_v == 1;

# pass two to figure out other remote TEMS, FTO backup hub TEMS is skipped
for (my $i=0;$i<=$nsavei;$i++) {
   next if $nsave_o4online[$i] ne "Y";                 # ignore unless online
   next if $nsave_product[$i] ne "EM";                 # ignore unless it is its own thrunode
   next if $nsave[$i] eq $tems_hub;                    # ignore hub TEMS
   next if $nsave_thrunode[$i] ne $tems_hub;           # ignore unless TEMS is connected via the hub TEMS
   next if substr($nsave_affinities[$i],40,1) eq "O";  # ignore other HUB - meaning FTO hub TEMS which will be out of date
                                                       # this indicates "able to run policy microscope"
   $temsi += 1;
   $tems[$temsi] = $nsave[$i];                         # add TEMS as next entry in tems array
   $tems_ishub[$temsi] = 0;
   $temsx{$nsave[$i]} = $temsi;
}

# Get the TSITDESC and TNAME data from the hub TEMS

$sqlfile = $opt_work . $delim . "tsitdesc.sql";
$sSQL ="SELECT SITNAME,SITINFO,REEV_DAYS,REEV_TIME,PDT FROM O4SRV.TSITDESC";

get_data($sSQL,"tsitdesc");
print STDERR "Got TSITDESC from hub $tems_hub\n" if $opt_v == 1;

# gather TNAME

$sqlfile = $opt_work . $delim . "tname.sql";
$sSQL ="SELECT ID,FULLNAME FROM O4SRV.TNAME";

get_data($sSQL,"tname");
print STDERR "Got TNAME from hub $tems_hub\n" if $opt_v == 1;


$sqlfile = $opt_work . $delim . "tsitstsh.sql";
$sSQL ="SELECT SITNAME,DELTASTAT,ORIGINNODE,LCLTMSTMP,GBLTMSTMP,NODE,ATOMIZE,RESULTS FROM O4SRV.TSITSTSH";

for (my $t=0;$t<=$temsi;$t++){
   if ($wtemsi > 0) {
      next if !defined $wtems{$tems[$t]};
   }
$DB::single=2;
   if ($tems[$t] eq $tems_hub) {
      get_data($sSQL,"tsitstsh");
print STDERR "Got TSITSTSH from hub TEMS $tems_hub\n" if $opt_v == 1;
   } else {
      get_data($sSQL,"tsitstsh",$tems[$t]);
print STDERR "Got TSITSTSH from remote TEMS $tems[$t]\n" if $opt_v == 1;
   }
}
$DB::single=2;
my $x = 1;

print STDERR "Finished\n" if $opt_v == 1;

exit 0;

sub get_data {
   my $iSQL = shift;
   my $itable = shift;
   my $iAT = shift;
   $iSQL .= " AT('" . $iAT . "')" if defined $iAT;

   my $target;
   $target = $iAT  if defined $iAT;
   $target = "hub" if !defined $iAT;
   $target =~ s/\:/\_/g if $gWin == 1;             # for Windows, convert any illegal colon : to an underline _ character
   $lstfile = $target . "." . $itable . ".lst";  # record each capture in a separate file, useful for debugging issues
   $lstfile = uc $lstfile;
   my $lstfn = $opt_work . $delim . $lstfile;      # record each capture in a separate file, useful for debugging issues

   my $sfile;

   open $sfile,">$sqlfile" or die "unable to open sql file $sqlfile";
   print $sfile "$iSQL\n";
   close $sfile;
   if ($gWin == 1) {
     # KfwSQLClient /v /f c:\temp\test.sql  >c:\temp\test.lst
     $ksc = $opt_home . '\cnps\KfwSQLClient /v /f ' . $sqlfile . '>' . $lstfn;
   } else {
     # /opt/IBM/ITM/bin/itmcmd execute cq "KfwSQLClient /v /f /tmp/itcamyn.sql"
     $ksc = $opt_home . '/bin/itmcmd execute cq "KfwSQLClient /f ' . $sqlfile . '"  >' . $lstfn;
   }

   $rc = system($ksc);
}

sub parse_lst {
  my ($lcount,$inline,$cref) = @_;            # count of desired chunks and the input line
  my @retlist = ();                     # an array of strings to return
  my $chunk = "";                       # One chunk
  my $oct = 1;                          # output chunk count
  my $rest;                             # the rest of the line to process
  $inline =~ /\]\s*(.*)/;               # skip by [NNN]  field
  $rest = " " . $1 . "        ";
  my $fixed;
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
     $fixed = $cref->{$oct};
     if (defined $fixed) {
        $chunk = substr($rest,$restpos+1,$fixed);
        push @retlist, $chunk;                 # record null data chunk
        $restpos += 2 + $fixed;
        $chunk = "";
        $oct += 1;
        next;
     }
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

sub new_inodests {
   my ($iexpirytime,$igbltmstmp,$ihostaddr,$ihostinfo,$inode,$io4online,$iproduct,$ireserved,$ithrunode,$iversion,$iaffinities) = @_;
   if (($io4online eq "Y") or ($opt_off == 1)) {
      $nsx = $nsavex{$inode};
      if (!defined $nsx) {
         $nsavei++;
         $nsx = $nsavei;
         $nsave[$nsx] = $inode;
         $nsavex{$inode} = $nsx;
         $nsave_expirytime[$nsx] = $iexpirytime;
         $nsave_gbltmstmp[$nsx] = $igbltmstmp;
         $nsave_hostaddr[$nsx] = $ihostaddr;
         $nsave_hostinfo[$nsx] = $ihostinfo;
         $nsave_o4online[$nsx] = $io4online;
         $nsave_product[$nsx] = $iproduct;
         $nsave_reserved[$nsx] = $ireserved;
         $nsave_thrunode[$nsx] = $ithrunode;
         $nsave_version[$nsx] = $iversion;
         $nsave_affinities[$nsx] = $iaffinities;
      }
   }

}


sub get_inodests {
   my $iSQL = shift;
   my $iAT = shift;
   $iSQL .= " AT('" . $iAT . "')" if defined $iAT;

   my $target;
   $target = $iAT  if defined $iAT;
   $target = "hub" if !defined $iAT;
   $target =~ s/\:/\_/g if $gWin == 1;             # for Windows, convert the illegal colon : to an underline _ character
   $lstfile = $target . '.inodests.lst';  # record each capture in a separate file, useful for debugging issues
   $lstfile = uc $lstfile;
   my $lstfn = $opt_work . $delim . $lstfile;  # record each capture in a separate file, useful for debugging issues

   my $sfile;

   if ($opt_redo == 0) {
      open $sfile,">$sqlfile" or die "unable to open sql file $sqlfile";
      print $sfile "$iSQL\n";
      close $sfile;
      if ($gWin == 1) {
        # KfwSQLClient /v /f c:\temp\test.sql  >c:\temp\test.lst
        $ksc = $opt_home . '\cnps\KfwSQLClient /v /f ' . $sqlfile . '>' . $lstfn;
      } else {
        # /opt/IBM/ITM/bin/itmcmd execute cq "KfwSQLClient /v /f /tmp/itcamyn.sql"
        $ksc = $opt_home . '/bin/itmcmd execute cq "KfwSQLClient /f ' . $sqlfile . '"  >' . $lstfn;
      }

      $rc = system($ksc);
   }

   my @knod_data;
   my $iexpirytime;
   my $igbltmstmp;
   my $ihostaddr;
   my $ihostinfo;
   my $inode;
   my $io4online;
   my $iproduct;
   my $ireserved;
   my $ithrunode;
   my $iversion;
   my $iaffinities;
   if (-f $lstfn) {

      open(KNOD, "< $lstfile") || die("Could not open INODESTS $lstfile\n");
      @knod_data = <KNOD>;
      close(KNOD);

      # Get data for all INODESTS records
      $ll = 0;
      foreach $oneline (@knod_data) {
         $ll += 1;
         next if substr($oneline,0,1) ne "[";                    # Look for starting point
         chop $oneline;
         if ($opt_aff == 0 ) {
            ($iexpirytime,$igbltmstmp,$ihostaddr,$ihostinfo,$inode,$io4online,$iproduct,$ireserved,$ithrunode,$iversion,$iaffinities) = parse_lst(11,$oneline);
         } else {                     # handle some earlier form of SQL
             my %cref = (1=>43,);
            ($iaffinities,$iexpirytime,$igbltmstmp,$ihostaddr,$ihostinfo,$inode,$io4online,$iproduct,$ireserved,$ithrunode,$iversion) = parse_lst(11,$oneline,\%cref);
         }
         $iexpirytime =~ s/\s+$//;   #trim trailing whitespace
         $igbltmstmp =~ s/\s+$//;    #trim trailing whitespace
         $ihostaddr =~ s/\s+$//;     #trim trailing whitespace
         $ihostinfo =~ s/\s+$//;     #trim trailing whitespace
         $inode =~ s/\s+$//;         #trim trailing whitespace
         $io4online =~ s/\s+$//;     #trim trailing whitespace
         $iproduct =~ s/\s+$//;      #trim trailing whitespace
         $ireserved =~ s/\s+$//;     #trim trailing whitespace
         $ithrunode =~ s/\s+$//;     #trim trailing whitespace
         $iversion =~ s/\s+$//;      #trim trailing whitespace
         $iaffinities =~ s/\s+$//;   #trim trailing whitespace
         new_inodests($iexpirytime,$igbltmstmp,$ihostaddr,$ihostinfo,$inode,$io4online,$iproduct,$ireserved,$ithrunode,$iversion,$iaffinities);
      }
   }
}

# 1.10000 - initial publication
