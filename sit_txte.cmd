rem prepare txt files for sitcache.pl
perl \support\itm\bin\tems2sql.pl -txt -o -tlim 0 -s SITNAME -tc SITNAME,SITINFO,REEV_DAYS,REEV_TIME,PDT \support\itm\dat\kib.cat  QA1CSITF.DB
perl \support\itm\bin\tems2sql.pl -txt -o -s ID -tc ID,FULLNAME  \support\itm\dat\kib.cat  QA1DNAME.DB
perl \support\itm\bin\tems2sql.pl -txt -o -tr -s SITNAME -tlim 0 -tc SITNAME,DELTASTAT,ORIGINNODE,LCLTMSTMP,GBLTMSTMP,NODE,ATOMIZE,RESULTS \support\itm\dat\kib.cat  QA1CSTSH.DB
