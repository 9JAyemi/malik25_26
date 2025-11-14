// SVA checker for pg_to_PG
// Concise, complete functional equivalence + focused coverage
// Bind this checker to the DUT

module pg_to_PG_sva
(
  input  logic [15:0] p,
  input  logic [15:0] g,
  input  logic [3:0]  bp,
  input  logic [3:0]  bg
);

  // Sample on any combinational change
  event comb_ev;
  always @* -> comb_ev;

  // Reference functions (4-state clean, used with case equality)
  function automatic logic exp_bp(input int idx);
    automatic int base;
    base = 4*idx;
    exp_bp = p[base+3] & p[base+2] & p[base+1] & p[base+0];
  endfunction

  function automatic logic exp_bg(input int idx);
    automatic int base;
    base = 4*idx;
    exp_bg = g[base+3]
           | (p[base+3] & g[base+2])
           | (p[base+3] & p[base+2] & g[base+1])
           | (p[base+3] & p[base+2] & p[base+1] & g[base+0]);
  endfunction

  // Determinism: known inputs => known outputs
  a_no_x_when_inputs_known: assert property (@(comb_ev)
      !$isunknown({p,g}) |-> !$isunknown({bp,bg}))
    else $error("pg_to_PG: Outputs contain X/Z while inputs are known");

  // Blocked generate/propagate equivalence and coverage
  genvar i;
  generate
    for (i=0; i<4; i++) begin: blk
      localparam int B = 4*i;

      // Functional equivalence (4-state exact)
      a_bp_eq: assert property (@(comb_ev) bp[i] === exp_bp(i))
        else $error("pg_to_PG: bp[%0d] mismatch", i);

      a_bg_eq: assert property (@(comb_ev) bg[i] === exp_bg(i))
        else $error("pg_to_PG: bg[%0d] mismatch", i);

      // Basic toggle coverage
      c_bp0:   cover property (@(comb_ev) bp[i] == 1'b0);
      c_bp1:   cover property (@(comb_ev) bp[i] == 1'b1);
      c_bg0:   cover property (@(comb_ev) bg[i] == 1'b0);
      c_bg1:   cover property (@(comb_ev) bg[i] == 1'b1);

      // Term-by-term bg cause coverage (each OR term can raise bg)
      c_bg_term0: cover property (@(comb_ev) g[B+3] && (bg[i]===1));
      c_bg_term1: cover property (@(comb_ev) p[B+3] && g[B+2] && (bg[i]===1));
      c_bg_term2: cover property (@(comb_ev) p[B+3] && p[B+2] && g[B+1] && (bg[i]===1));
      c_bg_term3: cover property (@(comb_ev) p[B+3] && p[B+2] && p[B+1] && g[B+0] && (bg[i]===1));

      // bp=1 condition coverage (all propagates in block asserted)
      c_bp_all1: cover property (@(comb_ev) p[B+3] && p[B+2] && p[B+1] && p[B+0] && (bp[i]===1));
    end
  endgenerate

endmodule

// Bind into the DUT
bind pg_to_PG pg_to_PG_sva sva_i(.p(p), .g(g), .bp(bp), .bg(bg));