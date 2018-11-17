# Types

$$
  \text{ProjectJSON} =
    \left\{(name, contents) \in \text{String} \times \text{Item}^*\right\}
$$

\begin{align*}
  \text{Item} = 
         &\left\{ (name, type) \in
          \text{String} \times \text{IType}
      \mid \text{type} = \text{'file'}\right\} \\
    \cup &\left\{ (name, type, contents) \in
          \text{String} \times \text{IType} \times \text{Item}^*
      \mid \text{type} = \text{'folder'}\right\}  
\end{align*}

$$
  \text{IType} = \left\{\text{'file'}, \text{'folder'}\right\}
$$

$$
  \text{Path} = \text{String}^*
$$

z.B.
  $(\text{'src'}, \text{'java'}, \text{'main'}, \text{'Test.java'})
  \in \text{Path}$

  (In JS: `['src', 'java', 'main', 'Test.java']`)

# Functions

$$
  \text{showProject} \in \text{ProjectJSON} \rightarrow ()
$$

* displays a project structure in the sidebar

$$
  \text{onDoubleClick} \in (\text{IType} \times (\text{Path} \rightarrow ())) \rightarrow ()
$$

* the given function will be executed, if the user double clicks on an element
  within the project tree. The element must be of the given type, though.
* it will be given the file's path within the project tree as parameter

$$
  \text{onNewFile} \in (\text{Path} \rightarrow ()) \rightarrow ()
$$

* the given function will be executed, if the user wants to create a new file
  within the project structure, using the sidebar.
* it will be given the file's path within the project tree as parameter

$$
  \text{onNewFolder} \in (\text{Path} \rightarrow ()) \rightarrow ()
$$

* same as onNewFile, but for folders.

# JS Examples

## Usage of showProject

```javascript
showProject({
  'name': 'MyProject',
  'contents': [
    {
      'name': 'src',
      'type': 'folder',
      'contents': [
        {
          'name': 'java',
          'type': 'folder',
          'contents': [
            {
              'name': 'main',
              'type': 'folder',
              'contents': [
                {
                  'name': 'Main.java',
                  'type': 'file'
                },
                {
                  'name': 'Test.java',
                  'type': 'file'
                }
              ]
            }
          ]
        }
      ]
    },
    {
      'name': 'README.md',
      'type': 'file'
    }
  ]
});
```

## Usage of onDoubleClick

```javascript
onDoubleClick('file', (path) => {
  //...
  console.log('A file was double clicked on!');
  console.log(path);
  //...
});
```
