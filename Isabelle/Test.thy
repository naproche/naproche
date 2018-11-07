theory Test
  imports Naproche
begin

forthel_file "../examples/powerset.ftl"

declare [[forthel_prove = false]]
forthel_file "../examples/tarski.ftl"

end
