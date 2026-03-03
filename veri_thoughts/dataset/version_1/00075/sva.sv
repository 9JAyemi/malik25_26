// SVA for mux6: concise, high-quality checks and coverage

module mux6_sva #(parameter WIREWIDTH = 1)
(
  input  logic [2:0]            s,
  input  logic [WIREWIDTH:0]    d0, d1, d2, d3, d4, d5,
  input  logic [WIREWIDTH:0]    o
);

  // Helper mirrors DUT selection semantics (case with default->d5)
  function automatic logic [WIREWIDTH:0] sel
  (
    input logic [2:0]         fs,
    input logic [WIREWIDTH:0] fd0, fd1, fd2, fd3, fd4, fd5
  );
    case (fs)
      3'd0: sel = fd0;
      3'd1: sel = fd1;
      3'd2: sel = fd2;
      3'd3: sel = fd3;
      3'd4: sel = fd4;
      default: sel = fd5; // includes 3'd5, 3'd6, 3'd7, and X/Z on fs
    endcase
  endfunction

  // Core functional correctness (combinational, 4-state exact compare)
  property p_mux_correct;
    @(*) (o === sel(s,d0,d1,d2,d3,d4,d5));
  endproperty
  assert property (p_mux_correct)
    else $error("mux6: output mismatch: s=%0d o=%0h exp=%0h",
                s, o, sel(s,d0,d1,d2,d3,d4,d5));

  // Explicitly check X/Z on select routes to d5 (as implemented)
  property p_sel_x_routes_to_d5;
    @(*) $isunknown(s) |-> (o === d5);
  endproperty
  assert property (p_sel_x_routes_to_d5)
    else $error("mux6: unknown select must route to d5");

  // Functional coverage: exercise all select values and observe correct output
  cover property (@(*) (s===3'd0) && (o===d0));
  cover property (@(*) (s===3'd1) && (o===d1));
  cover property (@(*) (s===3'd2) && (o===d2));
  cover property (@(*) (s===3'd3) && (o===d3));
  cover property (@(*) (s===3'd4) && (o===d4));
  cover property (@(*) (s===3'd5) && (o===d5));
  cover property (@(*) (s===3'd6) && (o===d5));
  cover property (@(*) (s===3'd7) && (o===d5));
  cover property (@(*) $isunknown(s) && (o===d5)); // default path with X/Z select

endmodule

bind mux6 mux6_sva #(.WIREWIDTH(WIREWIDTH)) mux6_sva_i (.*);