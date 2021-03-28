FROM ubuntu:18.04
RUN apt-get update
RUN apt-get install -y gcc make sudo cmake apt-transport-https software-properties-common binutils g++
RUN apt-get install -y wget apt-transport-https gnupg python
RUN wget -qO - https://adoptopenjdk.jfrog.io/adoptopenjdk/api/gpg/key/public | sudo apt-key add -
RUN echo "deb https://adoptopenjdk.jfrog.io/adoptopenjdk/deb bionic main" | sudo tee /etc/apt/sources.list.d/adoptopenjdk.list 
RUN apt-get update
RUN apt-get -y install adoptopenjdk-11-hotspot
RUN mkdir /home/bounder

# 3. sbt
RUN echo "deb https://dl.bintray.com/sbt/debian /" | sudo tee -a /etc/apt/sources.list.d/sbt.list
RUN sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 2EE0EA64E40A89B84B2DF73499E82A75642AC823
RUN sudo apt-get update
RUN sudo apt-get install -y sbt

## Microsoft z3
ENV Z3_VERSION "4.5.0"
# install debian packages
RUN apt-get update -qq -y \
 && apt-get install binutils g++ make ant -y \
 && apt-get clean \
 && rm -rf /var/lib/apt/lists/* \
#
# download, compile and install Z3
 && Z3_DIR="$(mktemp -d)" \
 && cd "$Z3_DIR" \
 && wget -qO- https://github.com/Z3Prover/z3/archive/z3-${Z3_VERSION}.tar.gz | tar xz --strip-components=1 \
 && python scripts/mk_make.py --java \
 && cd build \
 && make \
 && sudo make install \
 && cd / \
 && rm -rf "$Z3_DIR"

RUN apt-get update
RUN apt-get install -y zip unzip curl

## Android SDK
# Set up environment variables
ENV ANDROID_HOME="/root/android-sdk-linux" \
    SDK_URL="https://dl.google.com/android/repository/commandlinetools-linux-6858069_latest.zip" \
    GRADLE_URL="https://services.gradle.org/distributions/gradle-4.5.1-all.zip"

#SDK_URL="https://dl.google.com/android/repository/sdk-tools-linux-3859397.zip" \

# Install Gradle
RUN cd /root \
  && wget $GRADLE_URL -O gradle.zip \
  && unzip gradle.zip \
  && mv gradle-4.5.1 gradle \
  && rm gradle.zip \
  && mkdir .gradle

ENV PATH="/root/gradle/bin:${ANDROID_HOME}/cmdline-tools:${ANDROID_HOME}/platform-tools:${PATH}"

#ENV JAVA_OPTS="-XX:+IgnoreUnrecognizedVMOptions --add-modules java.se.ee"

# Download Android SDK
RUN mkdir "$ANDROID_HOME" .android \
  && cd "$ANDROID_HOME" \
  && curl -o sdk.zip $SDK_URL \
  && unzip sdk.zip \
  && rm sdk.zip \
  && cd $ANDROID_HOME/cmdline-tools/bin \
  && yes | ./sdkmanager --licenses --sdk_root=$ANDROID_HOME #\
  && touch /root/.android/repositories.cfg

# Install platform tools
RUN cd /root/android-sdk-linux/cmdline-tools/bin \
    && ./sdkmanager --sdk_root=$ANDROID_HOME "platform-tools" "platforms;android-10" "platforms;android-11" "platforms;android-12" "platforms;android-13" "platforms;android-14" "platforms;android-15" "platforms;android-16" "platforms;android-17" "platforms;android-18" "platforms;android-19" "platforms;android-20" "platforms;android-21" "platforms;android-22" "platforms;android-23" "platforms;android-24" "platforms;android-25" "platforms;android-26" "platforms;android-27" "platforms;android-7" "platforms;android-8" "platforms;android-9"
#
RUN  cd /root/android-sdk-linux/cmdline-tools/bin \
    && ./sdkmanager --sdk_root=$ANDROID_HOME "platforms;android-29"

RUN apt-get update
RUN apt-get install -y sqlite

COPY . /home/bounder/
ENV LD_LIBRARY_PATH=/usr/lib/
RUN cd /home/bounder/; sbt assembly

RUN mkdir /home/bounder_host

CMD ["/bin/bash"]
