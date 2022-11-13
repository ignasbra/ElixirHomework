defmodule DistSysNaive.MixProject do
  use Mix.Project

  def project do
    [
      app: :dist_sys_naive,
      version: "0.1.0",
      elixir: "~> 1.13",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      releases: [
        dss: [include_executables_for: [:unix]]
      ]
    ]
  end

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger],
      mod: {DistSysNaive.App, []}
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      {:local_cluster, "~> 1.2"}, # This library is a utility library to offer easier testing of distributed clusters for Elixir. It offers very minimal shimming above several built in Erlang features to provide seamless node creations, especially useful when testing distributed applications.
      {:syn, "~> 3.3"}, # Syn (short for synonym) is a scalable global Process Registry and Process Group manager for Erlang and Elixir, able to automatically manage dynamic clusters (addition / removal of nodes) and to recover from net splits.
      {:plug_cowboy, "~> 2.5"}, # Cowboy is a small, fast and modern HTTP server for Erlang/OTP. A Plug Adapter for the Erlang Cowboy web server.
      {:jason, "~> 1.3"}
    ]
  end
end
