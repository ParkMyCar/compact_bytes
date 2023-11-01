<div align="center">
  <h1><code>compact_bytes</code></h1>
  <p><strong>A memory efficient bytes container that can store up to 23 bytes on the stack.</strong></p>
</div>

<br />
<br />
<br />

### Note from the Maintainer
This crate was mostly developed for [`Materialize`](https://github.com/MaterializeInc/materialize) out of a need for a more compact bytes container. It entirely borrows implementation from
[`compact_str`](https://github.com/ParkMyCar/compact_str) which has been thoughtfully maintained over the past few years by a number of dedicated contributors, including:

* [NobodyXu](https://github.com/NobodyXu)
* [Kijewski](https://github.com/Kijewski)
* [matklad](https://github.com/matklad)
* [CAD97](https://github.com/CAD97)
* [mcronce](https://github.com/mcronce)
* [neoeinstein](https://github.com/neoeinstein)
* [tylerhawkes](https://github.com/tylerhawkes)
* [dragazo](https://github.com/dragazo)
* [Nilstrieb](https://github.com/Nilstrieb)
* [njaard](https://github.com/njaard)
* [vipentii](https://github.com/vipentti)
* [vbasky](https://github.com/vbasky)
* [mishrasamiksha](https://github.com/mishrasamiksha)

For now this repository exists separately from `compact_str` because it's easier to get started that way. But the plan is to eventually merge the two.
