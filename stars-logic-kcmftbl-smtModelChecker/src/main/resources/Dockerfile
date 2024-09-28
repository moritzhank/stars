FROM python:3.9-slim-bullseye

RUN apt-get update
RUN apt-get install -y wget
RUN apt-get install -y unzip
RUN apt-get install -y default-jre

WORKDIR /root
COPY install.py .
RUN python3 install.py

RUN rm install.py
RUN apt-get install -y z3
RUN apt-get autoremove -y wget
RUN apt-get autoremove -y unzip

COPY dispatcher.jar .
EXPOSE 7500/tcp
ENTRYPOINT [ "java", "-jar", "dispatcher.jar"]