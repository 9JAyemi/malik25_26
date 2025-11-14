// SVA for up_down_counter
module up_down_counter_sva #(parameter WIDTH=4) (
  input logic                    clk,
  input logic                    clear,
  input logic                    load,
  input logic                    up_down,
  input logic [WIDTH-1:0]        data,
  input logic [WIDTH-1:0]        count
);

  logic past_v;
  always_ff @(posedge clk) past_v <= 1'b1;

  function automatic [WIDTH-1:0] mod_inc(input [WIDTH-1:0] v);
    mod_inc = (v + 1) & {WIDTH{1'b1}};
  endfunction

  function automatic [WIDTH-1:0] mod_dec(input [WIDTH-1:0] v);
    mod_dec = (v - 1) & {WIDTH{1'b1}};
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Core functional behavior with priority: clear > load > up_down > down
  assert property (past_v |-> (
     $past(clear)      ? (count == '0) :
     $past(load)       ? (count == $past(data)) :
     $past(up_down)    ? (count == mod_inc($past(count))) :
                         (count == mod_dec($past(count)))
  )) else $error("Functional mismatch");

  // Sanity: no X/Z on any observed signal
  assert property (past_v |-> !$isunknown({clear,load,up_down,data,count}))
    else $error("X/Z detected on inputs/outputs");

  // Coverage: each branch, including wraparounds and priority overlaps
  cover property (past_v && $past(clear) && count == '0);
  cover property (past_v && !$past(clear) && $past(load) && count == $past(data));

  cover property (past_v && !$past(clear) && !$past(load) && $past(up_down) &&
                  $past(count) != {WIDTH{1'b1}} && count == mod_inc($past(count)));
  cover property (past_v && !$past(clear) && !$past(load) && $past(up_down) &&
                  $past(count) == {WIDTH{1'b1}} && count == '0);

  cover property (past_v && !$past(clear) && !$past(load) && !$past(up_down) &&
                  $past(count) != '0 && count == mod_dec($past(count)));
  cover property (past_v && !$past(clear) && !$past(load) && !$past(up_down) &&
                  $past(count) == '0 && count == {WIDTH{1'b1}});

  // Priority overlap coverage
  cover property (past_v && $past(clear && load) && count == '0);
  cover property (past_v && $past(!clear && load && up_down) && count == $past(data));

endmodule

bind up_down_counter up_down_counter_sva #(.WIDTH(4)) u_up_down_counter_sva (
  .clk(clk), .clear(clear), .load(load), .up_down(up_down), .data(data), .count(count)
);