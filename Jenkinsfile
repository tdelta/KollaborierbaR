pipeline {
    agent {
        label 'master'
    }
    environment {
        RUNNING_IN_JENKINS = 'true'
    }
    stages {
        stage('Setup') {
            steps {
              sh 'make setup'
            }
        }
        stage('Static Analysis') {
            steps {
              sh 'make check'
            }
        }
        stage('Build') {
            steps {
              sh 'make'
            }
        }
        stage('Tests') {
            steps {
              sh 'make test'
            }
        }
    }
}
