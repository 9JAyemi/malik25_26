// SVA for OSERDESE2
// Bind these assertions to the DUT instance
// Focus: correctness of parallel load, shift behavior, OQ muxing, and tied-offs

module OSERDESE2_sva (
  input  logic        CLK,
  input  logic        CLKDIV,
  input  logic        RST,
  input  logic        OQ,
  input  logic        OFB, TQ, TBYTEOUT, SHIFTOUT1, SHIFTOUT2, TFB,
  input  logic        D1, D2, D3, D4, D5, D6, D7, D8,
  input  logic [7:0]  buffer,
  input  logic [3:0]  even,
  input  logic [3:0]  odd,
  input  logic [1:0]  clkdiv_sample
);

  // Recreate the DUT's internal wire
  wire load_parallel = (clkdiv_sample == 2'b00);

  // Constants tied off
  assert property (@(posedge CLK or negedge CLK) disable iff (RST)
                   (OFB==1'b0 && TQ==1'b0 && TBYTEOUT==1'b0 &&
                    SHIFTOUT1==1'b0 && SHIFTOUT2==1'b0 && TFB==1'b0));

  // OQ muxing correctness
  assert property (@(posedge CLK) disable iff (RST) OQ == even[0]);
  assert property (@(negedge CLK) disable iff (RST) OQ == odd[0]);

  // Avoid unknown on OQ during operation
  assert property (@(posedge CLK or negedge CLK) disable iff (RST) !$isunknown(OQ));

  // buffer loads on CLKDIV posedge
  assert property (@(posedge CLKDIV) disable iff (RST)
                   ##0 buffer == {D8,D7,D6,D5,D4,D3,D2,D1});

  // clkdiv_sample shift on CLK negedge: {old bit0, current CLKDIV}
  assert property (@(negedge CLK) disable iff (RST)
                   ##0 clkdiv_sample == {$past(clkdiv_sample[0]), CLKDIV});

  // even/odd parallel load when load_parallel is true at CLK posedge
  assert property (@(posedge CLK) disable iff (RST)
                   load_parallel |-> ##0 even == {buffer[6],buffer[4],buffer[2],buffer[0]});
  assert property (@(posedge CLK) disable iff (RST)
                   load_parallel |-> ##0 odd  == {buffer[7],buffer[5],buffer[3],buffer[1]});

  // even/odd shift-right with zero fill when not loading
  assert property (@(posedge CLK) disable iff (RST)
                   !load_parallel |-> ##0 even == {1'b0, $past(even[3:1])});
  assert property (@(posedge CLK) disable iff (RST)
                   !load_parallel |-> ##0 odd  == {1'b0, $past(odd[3:1])});

  // After 4 consecutive non-load cycles, both shift registers must drain to zero
  assert property (@(posedge CLK) disable iff (RST)
                   (!load_parallel)[*4] |-> (even==4'b0000 && odd==4'b0000));

  // End-to-end serialization: after a load at a CLK posedge, OQ must emit bits 0..7
  // across the next 8 CLK edges (pos,neg,...)
  property p_serialize8;
    bit [7:0] b;
    @(posedge CLK or negedge CLK) disable iff (RST)
      (load_parallel && CLK, b = buffer)
        |-> (OQ==b[0]) ##1 (OQ==b[1]) ##1 (OQ==b[2]) ##1 (OQ==b[3])
            ##1 (OQ==b[4]) ##1 (OQ==b[5]) ##1 (OQ==b[6]) ##1 (OQ==b[7]);
  endproperty
  assert property (p_serialize8);

  // Coverage: see both load and shift behaviors and a full serialization burst
  cover property (@(posedge CLK) load_parallel);
  cover property (@(posedge CLK) !load_parallel);
  cover property (p_serialize8);

endmodule

bind OSERDESE2 OSERDESE2_sva i_oserdese2_sva (.*);