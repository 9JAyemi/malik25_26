// SVA for up_counter_3bit
module up_counter_3bit_sva (
  input logic       clk,
  input logic       rst,      // active-low async reset
  input logic [2:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (@(posedge clk) !$isunknown({rst,count}));

  // Asynchronous reset clears immediately
  assert property (@(negedge rst) ##0 (count == 3'b000));

  // Hold zero while in reset
  assert property ( !rst |-> (count == 3'b000) );

  // Functional step when not in reset
  assert property ( disable iff (!rst)
                    (count != 3'b111) |=> (count == $past(count) + 3'b001) );
  assert property ( disable iff (!rst)
                    (count == 3'b111) |=> (count == 3'b000) );

  // First increment after reset release
  assert property ( $rose(rst) |=> (count == 3'b001) );

  // Coverage
  cover property (@(negedge rst) 1);                  // saw reset assert
  cover property ( $rose(rst) );                      // saw reset deassert
  cover property ( disable iff (!rst)
                   (count == 3'b111) ##1 (count == 3'b000) ); // wrap 7->0
  // Full cycle after reset release: 1..7->0->1
  cover property ( $rose(rst)
                   ##1 (count==3'b001) ##1 (count==3'b010) ##1 (count==3'b011)
                   ##1 (count==3'b100) ##1 (count==3'b101) ##1 (count==3'b110)
                   ##1 (count==3'b111) ##1 (count==3'b000) ##1 (count==3'b001) );

endmodule

// Bind into DUT
bind up_counter_3bit up_counter_3bit_sva sva_u ( .clk(clk), .rst(rst), .count(count) );