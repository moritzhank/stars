FROM python:3.9-slim-bullseye

RUN apt-get update
RUN apt-get install -y wget
RUN apt-get install -y unzip

WORKDIR /root
COPY install.py .
RUN python3 install.py

RUN rm install.py
RUN apt-get autoremove -y wget
RUN apt-get autoremove -y unzip

COPY run.py .
ENTRYPOINT [ "python3", "run.py" ]