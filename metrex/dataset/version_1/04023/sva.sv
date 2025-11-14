// SVA checkers for mux_parity and mux_4to1
// Provide a sampling clock/reset from your TB when binding.

module mux_parity_sva #(parameter WIDTH=8) (
  input logic                 clk,
  input logic                 rst_n,
  input logic [WIDTH-1:0]     a,b,c,d,
  input logic                 sel_a, sel_b,
  input logic [WIDTH-1:0]     out,
  input logic                 error_flag
);
  logic [WIDTH-1:0] chosen;
  always_comb begin
    unique case ({sel_a, sel_b})
      2'b00: chosen = a;
      2'b01: chosen = b;
      2'b10: chosen = c;
      2'b11: chosen = d;
      default: chosen = 'x;
    endcase
  end

  // Knownness guard: when select and chosen data are known
  wire guard = !$isunknown({sel_a, sel_b}) && !$isunknown(chosen);

  // Error flag equals parity of selected data
  assert property (@(posedge clk) disable iff (!rst_n)
    guard |-> ##0 (error_flag === (^chosen)));

  // Output behavior for odd/even parity
  assert property (@(posedge clk) disable iff (!rst_n)
    (guard && (^chosen)) |-> ##0 (error_flag && (out == '0)));

  assert property (@(posedge clk) disable iff (!rst_n)
    (guard && !(^chosen)) |-> ##0 (!error_flag && (out === chosen)));

  // Error implies zeroed output (one-way)
  assert property (@(posedge clk) disable iff (!rst_n)
    error_flag |-> ##0 (out == '0));

  // If all inputs and selects are known, outputs must be known
  assert property (@(posedge clk) disable iff (!rst_n)
    (!$isunknown({a,b,c,d,sel_a,sel_b})) |-> ##0 !$isunknown({out,error_flag}));

  // Functional coverage: each select with both parity outcomes
  cover property (@(posedge clk) disable iff (!rst_n)
    ({sel_a,sel_b}==2'b00 && (^a)==0 && out==a && !error_flag));
  cover property (@(posedge clk) disable iff (!rst_n)
    ({sel_a,sel_b}==2'b00 && (^a)==1 && out=='0 &&  error_flag));

  cover property (@(posedge clk) disable iff (!rst_n)
    ({sel_a,sel_b}==2'b01 && (^b)==0 && out==b && !error_flag));
  cover property (@(posedge clk) disable iff (!rst_n)
    ({sel_a,sel_b}==2'b01 && (^b)==1 && out=='0 &&  error_flag));

  cover property (@(posedge clk) disable iff (!rst_n)
    ({sel_a,sel_b}==2'b10 && (^c)==0 && out==c && !error_flag));
  cover property (@(posedge clk) disable iff (!rst_n)
    ({sel_a,sel_b}==2'b10 && (^c)==1 && out=='0 &&  error_flag));

  cover property (@(posedge clk) disable iff (!rst_n)
    ({sel_a,sel_b}==2'b11 && (^d)==0 && out==d && !error_flag));
  cover property (@(posedge clk) disable iff (!rst_n)
    ({sel_a,sel_b}==2'b11 && (^d)==1 && out=='0 &&  error_flag));
endmodule


module mux_4to1_sva #(parameter WIDTH=8) (
  input logic                 clk,
  input logic                 rst_n,
  input logic [WIDTH-1:0]     a,b,c,d,
  input logic                 sel_a, sel_b,
  input logic [WIDTH-1:0]     out
);
  logic [WIDTH-1:0] chosen;
  always_comb begin
    unique case ({sel_a, sel_b})
      2'b00: chosen = a;
      2'b01: chosen = b;
      2'b10: chosen = c;
      2'b11: chosen = d;
      default: chosen = 'x;
    endcase
  end

  wire guard = !$isunknown({sel_a, sel_b}) && !$isunknown(chosen);

  // MUX correctness (combinational, same-cycle)
  assert property (@(posedge clk) disable iff (!rst_n)
    guard |-> ##0 (out === chosen));

  // If all inputs and selects are known, output must be known
  assert property (@(posedge clk) disable iff (!rst_n)
    (!$isunknown({a,b,c,d,sel_a,sel_b})) |-> ##0 !$isunknown(out));

  // Functional coverage: exercise all select encodings
  cover property (@(posedge clk) disable iff (!rst_n) ({sel_a,sel_b}==2'b00));
  cover property (@(posedge clk) disable iff (!rst_n) ({sel_a,sel_b}==2'b01));
  cover property (@(posedge clk) disable iff (!rst_n) ({sel_a,sel_b}==2'b10));
  cover property (@(posedge clk) disable iff (!rst_n) ({sel_a,sel_b}==2'b11));
endmodule

// Example bind (connect clk/rst from your TB)
// bind mux_parity mux_parity_sva #(.WIDTH(8)) u_mux_parity_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));
// bind mux_4to1   mux_4to1_sva   #(.WIDTH(8)) u_mux_4to1_sva   (.* , .clk(tb_clk), .rst_n(tb_rst_n));