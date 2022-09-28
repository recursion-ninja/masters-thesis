Extract EPS images from original manuscript via the two sequences of commands:

```
pdftk Security\ Analysis\ and\ Improvements\ for\ the\ IETF\ MLS\ Standard\ for\ Group\ Messaging.pdf \
cat 6-6 output CGKA-page-6.pdf && \
pdfcrop --margins '0 0 0 0' --bbox '72 476 542 722' --clip CGKA-page-6.pdf CGKA-page-6-crop.pdf && \
pdftops -eps -r 1200 CGKA-page-6-crop.pdf && \
mv CGKA-page-6-crop.eps CGKA-Oracles.eps && \
rm CGKA-page-6*.pdf
```

```
pdftk Security\ Analysis\ and\ Improvements\ for\ the\ IETF\ MLS\ Standard\ for\ Group\ Messaging.pdf \
cat 9-9 output CGKA-page-9.pdf && \
pdfcrop --margins '0 0 0 0' --bbox '137 489 474 719' --clip CGKA-page-9.pdf CGKA-page-9-crop.pdf && \
pdftops -eps -r 1200 CGKA-page-9-crop.pdf && \
mv CGKA-page-9-crop.eps CGKA-TreeKEM-Secrets.eps && \
rm CGKA-page-9*.pdf
```
