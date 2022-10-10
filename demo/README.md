CPP 2023 submission 33
----------------------

UPDATE on 2022-10-10:

> * It was discovered post submission that the drag-and-drop feature was not
>   working on Chrome-based browsers because of a long standing Chrome bug:
>
>   https://bugs.chromium.org/p/chromium/issues/detail?id=501655
>
> * A workaround has been implemented for such browsers.
>
> * The version on github.io will be updated with the current version of the
>   code base. Unfortunately, this version has had a lot of changes since the
>   CPP2023 submission. This version will therefore be out of sync with the
>   submission. However, it is quite complicated to backport the fix to the old
>   version. This situation is regrettable.
>
> * The present version of this tool is mainly more "hands off" compared to the
>   CPP2023 submission version. In particular, many existential instantations
>   are guessed automatically.


Instructions:

* The `Profound-Intuitionistic` tool (aka `Profint`) is provided as a
  HTML+JavaScript application that runs largely inside a browser.

* It is recommended that you use a HTTP server, since serving from `file://`
  urls has not been been thoroughly tested.

* For example, Python 3 has a simple HTTP server as part of its standard
  library. To run it, execute the following command from the directory
  containing this very file:

       python3 -m http.server 8000

  You may change the port number if necessary. Other lightweight HTTP servers
  may, obviously, also be used.

* To run the tool, then, point a modern web browser to the URL/port of the local
  HTTP server. For example:

       xdg-open http://127.0.0.1:8000/

  (Replace `xdg-open` with any other browser if you want, such as `firefox`,
  `google-chrome`, etc.)

* The `Profint` tool packages all its dependencies together, and there should be
  no network requests that are triggered to the general internet. This can be
  verified by means of the "network monitor" tab or the equivalent in the
  developer tools section of the browser. In Firefox, for instance, this is
  accessed with the "Menu Button > More Tools > Web Developer Tools" (or by
  pressing Ctrl+Shift+I).

* A fully anonymized version of this tool is also being uploaded to Github at
  the following bespoke url: https://cpp2023p33.github.io/

  This will run a version that is identical to that which is uploaded to the CPP
  2023 site. It is being provided merely as a convenience for reviewers who
  choose to use it.
