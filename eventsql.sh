#!/bin/sh
# Set CANDLEHOME before starting or alter the next line to set installation directory for TEPS
if [ "$CANDLEHOME" = "" ]; then export CANDLEHOME=/opt/IBM/ITM; fi
${CANDLEHOME}/bin/itmcmd execute cq 'KfwSQLClient /e "SELECT SITNAME,SITINFO,REEV_DAYS,REEV_TIME,PDT FROM O4SRV.TSITDESC"' >QA1CSITF.DB.LST
${CANDLEHOME}/bin/itmcmd execute cq 'KfwSQLClient /e "SELECT ID,FULLNAME FROM O4SRV.TNAME"' >QA1DNAME.DB.LST
${CANDLEHOME}/bin/itmcmd execute cq 'KfwSQLClient /e "SELECT SITNAME,DELTASTAT,ORIGINNODE,LCLTMSTMP,NODE,ATOMIZE FROM O4SRV.QA1CSTSH"' >QA1CSTSH.DB.LST
