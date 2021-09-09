clean:
	$(RM) -r jscpd_report.txt _reports
	find . -iname _build -exec rm {} \; || echo "no build artifacts"
