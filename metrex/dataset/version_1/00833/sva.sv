// SVA for mux8: concise, full functional checks and key coverage
// Bind this module to mux8 instances from your testbench.
//
// Example bind:
// bind mux8 mux8_sva #(.WIDTH(WIDTH), .DISABLED(DISABLED)) u_mux8_sva (
//   .clk(tb_clk), .rst_n(tb_rst_n),
//   .en(en), .sel(sel), .i0(i0), .i1(i1), .i2(i2), .i3(i3),
//   .i4(i4), .i5(i5), .i6(i6), .i7(i7), .o(o)
// );

module mux8_sva #(parameter int WIDTH=32, parameter int DISABLED=0)
(
  input  logic                   clk,
  input  logic                   rst_n,
  input  logic                   en,
  input  logic [2:0]             sel,
  input  logic [WIDTH-1:0]       i0,i1,i2,i3,i4,i5,i6,i7,
  input  logic [WIDTH-1:0]       o
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Width-accurate disabled value
  localparam logic [WIDTH-1:0] DISABLED_W = DISABLED;

  // Reference mux function
  function automatic logic [WIDTH-1:0] f_mux
    (input logic [2:0] s,
     input logic [WIDTH-1:0] fi0,fi1,fi2,fi3,fi4,fi5,fi6,fi7);
    unique case (s)
      3'd0: f_mux = fi0;
      3'd1: f_mux = fi1;
      3'd2: f_mux = fi2;
      3'd3: f_mux = fi3;
      3'd4: f_mux = fi4;
      3'd5: f_mux = fi5;
      3'd6: f_mux = fi6;
      3'd7: f_mux = fi7;
      default: f_mux = 'x;
    endcase
  endfunction

  // Core functional correctness
  assert property ( !en |-> (o == DISABLED_W) )
    else $error("mux8: o != DISABLED when en=0");

  assert property ( en |-> (o == f_mux(sel,i0,i1,i2,i3,i4,i5,i6,i7)) )
    else $error("mux8: enabled output mismatch vs selected input");

  // Known-ness: if inputs and select are known, output must be known
  assert property ( en && !$isunknown(sel) &&
                    !$isunknown(f_mux(sel,i0,i1,i2,i3,i4,i5,i6,i7))
                    |-> !$isunknown(o) )
    else $error("mux8: X/Z leaked to output with known select/input");

  // Stability: if selection and selected input are stable under en, o is stable
  assert property ( en && $stable(sel) &&
                    $stable(f_mux(sel,i0,i1,i2,i3,i4,i5,i6,i7))
                    |-> $stable(o) )
    else $error("mux8: output changed without sel/selected-input change");

  // Minimal functional coverage
  cover property ( !en );
  cover property ( en && sel==3'd0 );
  cover property ( en && sel==3'd1 );
  cover property ( en && sel==3'd2 );
  cover property ( en && sel==3'd3 );
  cover property ( en && sel==3'd4 );
  cover property ( en && sel==3'd5 );
  cover property ( en && sel==3'd6 );
  cover property ( en && sel==3'd7 );
  // Exercise dynamic behavior
  cover property ( en && $changed(sel) );
  cover property ( en && $changed(f_mux(sel,i0,i1,i2,i3,i4,i5,i6,i7)) );

endmodule