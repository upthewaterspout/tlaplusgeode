# tlaplusgeode
This is an example of using TLA+ to verify some properties of one of Geode's algorithms.

This example shows how geode solves the ships passing in the night problem for replicated regions. 

There are two TLA+ specs here:
 * ShipsPassing.tla - This is an example of how two concurrent updates to replicated data can "pass" each other, resulting in inconsistent state
 * ConcurrencyChecksShipsPassing.tla - This shows how Geode uses version checks to get eventual consistency.
 
 To use this project, [download](https://github.com/tlaplus/tlaplus/releases/tag/v1.5.6) the tla+ toolbox.  Then use the open spec link and type in the *full path* to the .tla file, eg /Users/dsmith/Documents/Code/tlaplus/tlaplusgeode/ShipsPassing.tla. In MacOs, you must manually type in the path.
 
 Run the module using the TLC Model Checker -> Run Model option.
 
 Each of these projects has an eventual consistency property they are validating. This says that eventually, all updaters will have the same value:
 
 ```
 EventualConsistency == <>[](\A x \in 1..NUM_UPDATERS : vals[x] = vals[1])
 ```
 
 For the ShipsPassing, this property will fail.
 
 To Learn about TLA+
  * https://learntla.com/introduction/
 
