FROM ubuntu:16.04

ADD . /firrtl

RUN \
  apt-get update && \
  apt-get install -y git openjdk-8-jdk curl && \
  curl -L -o sbt.deb http://dl.bintray.com/sbt/debian/sbt-1.2.7.deb && \
  dpkg -i sbt.deb && \
  apt-get update && \
  apt-get install sbt

WORKDIR "/firrtl"


