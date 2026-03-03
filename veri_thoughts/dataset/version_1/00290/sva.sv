// SVA for top_module
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  d1,
  input  logic [7:0]  d2,
  input  logic        select,
  input  logic [7:0]  q_active,
  input  logic [15:0] result,
  input  logic [7:0]  reg1,
  input  logic [7:0]  reg2,
  input  logic [3:0]  counter
);

  default clocking cb @(posedge clk); endclocking

  // Static design sanity (select width vs. case items)
  initial begin
    if ($bits(select) < 2)
      $error("select width (%0d) cannot represent case items 2 or 3; some functionality is unreachable", $bits(select));
  end

  // Reset behavior (synchronous, same edge)
  assert property (@(posedge clk) reset |-> (reg1==8'h34 && reg2==8'h34 && counter==4'h0));

  // Data path result
  assert property (@(posedge clk) result == {reg1,reg2});

  // Input X checks
  assert property (@(posedge clk) !$isunknown(select));
  assert property (disable iff (reset) (select==1) |-> !$isunknown(d1));
  assert property (disable iff (reset) (select==2) |-> !$isunknown(d2));

  // Hold when select==0 (no case item matches)
  assert property (disable iff (reset)
                   (select==1'b0) |=> (reg1==$past(reg1) && reg2==$past(reg2) && counter==$past(counter)));

  // Register and counter updates per intended case items
  // reg1 load on select==1
  assert property (disable iff (reset)
                   (select==1) |=> (reg1==$past(d1) && reg2==$past(reg2) && counter==$past(counter)));

  // reg2 load on select==2 (unreachable with 1-bit select, kept for spec coverage)
  assert property (disable iff (reset)
                   (select==2) |=> (reg2==$past(d2) && reg1==$past(reg1) && counter==$past(counter)));

  // counter increment on select==3 (unreachable with 1-bit select, kept for spec coverage)
  assert property (disable iff (reset)
                   (select==3 && counter!=4'hF) |=> (counter==$past(counter)+1 && reg1==$past(reg1) && reg2==$past(reg2)));
  assert property (disable iff (reset)
                   (select==3 && counter==4'hF) |=> (counter==4'h0 && reg1==$past(reg1) && reg2==$past(reg2)));

  // q_active mapping
  assert property (disable iff (reset)
                   (select==0) |-> (q_active[3:0]==counter && q_active[7:4]==4'h0));
  assert property (disable iff (reset)
                   (select==1) |-> (q_active==reg1));

  // Coverage
  cover property (@(posedge clk) reset ##1 !reset);
  cover property (disable iff (reset) (select==1));
  cover property (disable iff (reset) (select==2));     // should not hit with 1-bit select
  cover property (disable iff (reset) (select==3));     // should not hit with 1-bit select
  cover property (disable iff (reset) (select==3)[*16] ##1 (counter==4'h0)); // counter wrap scenario
endmodule

// Bind into DUT to access internals
bind top_module top_module_sva sva_i (
  .clk      (clk),
  .reset    (reset),
  .d1       (d1),
  .d2       (d2),
  .select   (select),
  .q_active (q_active),
  .result   (result),
  .reg1     (reg1),
  .reg2     (reg2),
  .counter  (counter)
);