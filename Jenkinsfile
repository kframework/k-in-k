pipeline {
  agent {
    dockerfile {
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  stages {
    stage("Init title") {
      when { changeRequest() }
      steps {
        script {
          currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
        }
      }
    }
    stage('Build') {
      steps {
        ansiColor('xterm') {
          sh '''#!/bin/bash
            (cd ext/k-light/ && mvn package -DskipTests) && ./build kink
          '''
        }
      }
    }
    stage('t/foobar') {
      steps {
        ansiColor('xterm') {
          sh '''#!/bin/bash
            ./build t/foobar
          '''
        }
      }
    }
    stage('t/peano') {
      steps {
        ansiColor('xterm') {
          sh '''#!/bin/bash
            ./build t/foobar
          '''
        }
      }
    }
    stage('t/*') {
      steps {
        ansiColor('xterm') {
          sh '''#!/bin/bash
            ./build
          '''
        }
      }
    }
  }
}
