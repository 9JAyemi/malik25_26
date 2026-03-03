// SVA checker for shift_register
module shift_register_sva #(
  parameter int WIDTH = 4
)(
  input  logic               CLK,
  input  logic               LOAD,
  input  logic [WIDTH-1:0]   DATA,
  input  logic [WIDTH-1:0]   Q,
  input  logic [WIDTH-1:0]   reg_out
);

  default clocking cb @(posedge CLK); endclocking

  // Guard for $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  // Q mirrors internal reg_out (observability)
  assert property (cb Q === reg_out)
    else $error("Q must mirror reg_out");

  // Exact next-state function (one concise assertion covers both branches)
  assert property (cb past_valid |-> Q == ($past(LOAD) ? $past(DATA)
                                                      : { $past(Q)[WIDTH-2:0], 1'b0 }))
    else $error("Next-state mismatch: LOAD vs shift behavior");

  // After WIDTH consecutive shifts (no LOAD), register must flush to zero
  sequence no_load_width; !LOAD[*WIDTH]; endsequence
  assert property (cb no_load_width |=> Q == '0)
    else $error("Did not flush to zero after WIDTH shifts");

  // Coverage
  cover property (cb LOAD);                         // took load path
  cover property (cb !LOAD);                        // took shift path
  cover property (cb LOAD ##1 !LOAD);               // load then shift
  cover property (cb LOAD[*2]);                     // back-to-back loads
  cover property (cb LOAD ##1 !LOAD[*WIDTH] ##1 Q == '0); // load then flush to zero
  cover property (cb (LOAD && DATA == {{(WIDTH-1){1'b0}},1'b1})
                      ##1 !LOAD[* (WIDTH-1) ] ##1
                      (Q == {1'b1, {(WIDTH-1){1'b0}}}));   // walk '1' to MSB

endmodule

// Bind into DUT (matches port names, including internal reg_out)
bind shift_register shift_register_sva #(.WIDTH(4)) shift_register_sva_i (.*);