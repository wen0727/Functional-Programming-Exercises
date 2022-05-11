namespace HelloWorld.Controllers
//The following content is for developing a web api by using F#, and the tutorial can be found through the link https://docs.microsoft.com/en-us/visualstudio/get-started/tutorial-fsharp-web-app?view=vs-2022
//libraries
open System
open System.Collections.Generic
open System.Linq
open System.Threading.Tasks
open Microsoft.AspNetCore.Mvc
open Microsoft.Extensions.Logging
open HelloWorld
//Attributes
[<ApiController>]
[<Route("[controller]")>]
//Type implementation with functions 
type WeatherForecastController (logger : ILogger<WeatherForecastController>) =
    inherit ControllerBase()
    //array of strings
    let summaries =
        [|
            "Freezing"
            "Bracing"
            "Chilly"
            "Cool"
            "Mild"
            "Warm"
            "Balmy"
            "Hot"
            "Sweltering"
            "Scorching"
        |]

    [<HttpGet>]
    member _.Get() =
        ////building array of a data type with RECORD data structure. 
        //let rng = System.Random()
        //[|
        //    for index in 0..4 ->
        //        { Date = DateTime.Now.AddDays(float index)
        //          TemperatureC = rng.Next(-20,55)
        //          Summary = summaries.[rng.Next(summaries.Length)] }
        //|]
        let helloWorld = [|"Hello"; "World"; "First F#/ASP.NET Core web API!"|] 
        //The asynchronous function call with parameter
        ActionResult<string[]>(helloWorld)
