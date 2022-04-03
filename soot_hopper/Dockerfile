#FROM ubuntu:18.04 # note: trying 20.04 because of glibc 2.29 req for infer
FROM ubuntu:20.04 
RUN apt-get update
RUN apt-get install -y gcc make sudo cmake apt-transport-https software-properties-common binutils g++ curl
RUN apt-get install -y wget apt-transport-https gnupg python
RUN wget -qO - https://adoptopenjdk.jfrog.io/adoptopenjdk/api/gpg/key/public | sudo apt-key add -
RUN echo "deb https://adoptopenjdk.jfrog.io/adoptopenjdk/deb bionic main" | sudo tee /etc/apt/sources.list.d/adoptopenjdk.list 
RUN apt-get update
RUN apt-get -y install adoptopenjdk-11-hotspot
RUN mkdir /home/bounder

## 3. sbt
#RUN echo "deb https://dl.bintray.com/sbt/debian /" | sudo tee -a /etc/apt/sources.list.d/sbt.list
#RUN sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 2EE0EA64E40A89B84B2DF73499E82A75642AC823
#RUN sudo apt-get update
#RUN sudo apt-get install -y sbt

# SBT
RUN echo "deb https://repo.scala-sbt.org/scalasbt/debian all main" | sudo tee /etc/apt/sources.list.d/sbt.list
RUN echo "deb https://repo.scala-sbt.org/scalasbt/debian /" | sudo tee /etc/apt/sources.list.d/sbt_old.list
RUN curl -sL "https://keyserver.ubuntu.com/pks/lookup?op=get&search=0x2EE0EA64E40A89B84B2DF73499E82A75642AC823" | sudo -H gpg --no-default-keyring --keyring gnupg-ring:/etc/apt/trusted.gpg.d/scalasbt-release.gpg --import
RUN sudo chmod 644 /etc/apt/trusted.gpg.d/scalasbt-release.gpg
RUN sudo apt-get update
RUN sudo apt-get install -y sbt

## Microsoft z3
ENV Z3_VERSION "4.8.10"
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
RUN apt-get install -y zip unzip

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
#  Note: commented out the following platforms since they are old and I don't think we use them anymore
# "platforms;android-10" "platforms;android-11" "platforms;android-12" "platforms;android-13" "platforms;android-14" "platforms;android-15"
RUN cd /root/android-sdk-linux/cmdline-tools/bin \
    && ./sdkmanager --sdk_root=$ANDROID_HOME "platform-tools"  "platforms;android-16" "platforms;android-17" "platforms;android-18" "platforms;android-19" "platforms;android-20" "platforms;android-21" "platforms;android-22" "platforms;android-23" "platforms;android-24" "platforms;android-25" "platforms;android-26" "platforms;android-27" "platforms;android-7" "platforms;android-8" "platforms;android-9" "platforms;android-30"
#
RUN  cd /root/android-sdk-linux/cmdline-tools/bin \
    && ./sdkmanager --sdk_root=$ANDROID_HOME "platforms;android-29"

RUN apt-get update
RUN apt-get install -y sqlite

ARG COMMITHASH=unknown
RUN echo $COMMITHASH >/home/bounder/commithash.txt
RUN rm -r /home/bounder 2>/dev/null

RUN mkdir /home/bounder_host
ENV BOUNDER_JAR=/home/bounder/target/scala-2.13/soot_hopper-assembly-0.1.jar

# Install infer for baseline comparison
# mkdir the man/man1 directory due to Debian bug #863199
RUN apt-get update && \
    mkdir -p /usr/share/man/man1 && \
    apt-get install --yes --no-install-recommends \
      libc6-dev \
      xz-utils \
      zlib1g-dev && \
    rm -rf /var/lib/apt/lists/*


# Download the Infer release
RUN INFER_VERSION=v1.1.0; \
    cd /opt && \
    curl -sL \
      https://github.com/facebook/infer/releases/download/${INFER_VERSION}/infer-linux64-${INFER_VERSION}.tar.xz | \
    tar xJ && \
    rm -f /infer && \
    ln -s ${PWD}/infer-linux64-$INFER_VERSION /infer

# Install infer
ENV PATH /infer/bin:${PATH}

RUN touch $(date +%s) # force rebuild from here every time to grab new jar
COPY . /home/bounder/
ENV LD_LIBRARY_PATH=/usr/lib/
#RUN cd /home/bounder/; sbt assembly



CMD ["/bin/bash"]
