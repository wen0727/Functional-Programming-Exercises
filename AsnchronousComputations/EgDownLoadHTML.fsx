//Uri, WebClient

open System.Net.Http
open Microsoft.FSharp.Control.WebExtensions

let urlList = [ "Microsoft.com", "http://www.microsoft.com/"
                "MSDN", "http://msdn.microsoft.com/"
                "Bing", "http://www.bing.com"
              ]

let fetchAsync(name, url:string) =
    async {
        try
            let request = new HttpClient()
            let! response = request.GetAsync(url) |> Async.AwaitTask
            response.EnsureSuccessStatusCode |> ignore
            let! content = response.Content.ReadAsStringAsync() |> Async.AwaitTask
            printfn "%s" (content)
        with
            | ex -> printfn "%s" (ex.Message);
    }

let runAll() =
    urlList
    |> Seq.map fetchAsync
    |> Async.Parallel
    |> Async.RunSynchronously
    |> ignore

runAll()