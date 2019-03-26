#!/bin/bash

set -e

mkdir -p deliverables/KollaborierbaR
mkdir deliverables/KollaborierbaR/projects

cp -R client/build/* deliverables/KollaborierbaR/
cp server/build/libs/KollaborierbaR-*.jar deliverables/KollaborierbaR/
cp tools/deploymentRun.sh deliverables/KollaborierbaR/run.sh

chmod +x deliverables/KollaborierbaR/run.sh
chmod +x deliverables/KollaborierbaR/KollaborierbaR-*.jar

cd deliverables
tar -cvzf KollaborierbaR.tar.gz KollaborierbaR/*
rm -rf KollaborierbaR
cd ..

echo "Deployed."

