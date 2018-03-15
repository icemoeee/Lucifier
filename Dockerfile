FROM ubuntu:rolling

LABEL maintainer "Luong Nguyen <luongnt.58@gmail.com>"

SHELL ["/bin/bash", "-c"]
RUN apt-get update
RUN apt-get install -y wget unzip python-virtualenv git build-essential software-properties-common curl
RUN add-apt-repository -y ppa:ethereum/ethereum-dev
RUN add-apt-repository -y ppa:ethereum/ethereum
RUN curl -sS https://dl.yarnpkg.com/debian/pubkey.gpg | apt-key add -
RUN echo "deb https://dl.yarnpkg.com/debian/ stable main" | tee /etc/apt/sources.list.d/yarn.list
RUN apt-get update
RUN apt-get install -y yarn
RUN apt-get install -y build-essential golang-go solc ethereum python python-pip \
            ruby ruby-rails ruby-dev rake git-core curl zlib1g-dev build-essential libssl-dev \
                        libreadline-dev npm libyaml-dev libsqlite3-dev sqlite3 libxml2-dev libxslt1-dev \
                        libcurl4-openssl-dev python-software-properties libffi-dev nodejs && \
     apt-get clean
RUN pip install requests web3 six z3-solver

COPY . /oyente/
WORKDIR /oyente/


# RUN cd /oyente/web && ./bin/yarn install
# RUN cd /oyente/web
# RUN rails --version
# RUN ruby --version
# RUN gem install bundler --version '1.14.6'
# RUN bundle install
# # RUN gem install bundler --version '1.14.6' --no-ri --no-rdoc && bundle in

# WORKDIR /oyente/web
# CMD ["./bin/rails", "server"]
