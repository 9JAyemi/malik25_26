// SVA for the design. Bind to top_module; no DUT edits required.

module top_module_sva (
  input  logic [7:0] in,
  input  logic [3:0] pos,
  input  logic [3:0] out
);

  // Combinational sampling for concurrent assertions/coverage
  clocking cb @(*);
  endclocking
  default clocking cb;

  // Reference priority function (matches DUT behavior: checks in[6:0], default=7)
  function automatic logic [2:0] prio7 (input logic [6:0] v);
    prio7 = 3'd7;
    if (v[0])      prio7 = 3'd0;
    else if (v[1]) prio7 = 3'd1;
    else if (v[2]) prio7 = 3'd2;
    else if (v[3]) prio7 = 3'd3;
    else if (v[4]) prio7 = 3'd4;
    else if (v[5]) prio7 = 3'd5;
    else if (v[6]) prio7 = 3'd6;
  endfunction

  // Priority encoder must match reference; pos is 4b but value must be 0..7
  ap_priority: assert property ( pos[3] == 1'b0 && pos[2:0] == prio7(in[6:0]) )
    else $error("priority_encoder mismatch: in=%b pos=%0d", in, pos);

  // Subtractor correctness
  ap_sub: assert property ( out == (pos - 4'd5) )
    else $error("subtractor mismatch: pos=%0d out=%0d", pos, out);

  // Functional coverage: each selected position 0..6 and the default 7
  cover property ( in[0] ##0 (pos[2:0] == 3'd0) );
  genvar gi;
  generate
    for (gi = 1; gi < 7; gi++) begin : GEN_POS_COV
      localparam logic [2:0] J = gi[2:0];
      cover property ( (!|in[gi-1:0]) && in[gi] ##0 (pos[2:0] == J) );
    end
  endgenerate
  cover property ( (~|in[6:0]) ##0 (pos[2:0] == 3'd7) );

  // Subtractor output coverage (all reachable outputs for pos=0..7)
  cover property (out == 4'hB);
  cover property (out == 4'hC);
  cover property (out == 4'hD);
  cover property (out == 4'hE);
  cover property (out == 4'hF);
  cover property (out == 4'h0);
  cover property (out == 4'h1);
  cover property (out == 4'h2);

endmodule

bind top_module top_module_sva u_top_module_sva(.in(in), .pos(pos), .out(out));