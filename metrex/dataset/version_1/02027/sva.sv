// SVA for mouse_painter
module mouse_painter_sva (
  input  logic        clk,
  input  logic        reset_n,   // active-low; tie high if unused
  input  logic [4:0]  line_number,
  input  logic [7:0]  line_code
);

  // Expected mapping function (spec-derived)
  function automatic logic [7:0] expected_line_code(input logic [4:0] ln);
    logic [8:0] tmp;
    if (ln <= 5'd7) begin
      tmp = (9'h1 << (ln + 1)) - 1;          // 2^(ln+1)-1
      return tmp[7:0];
    end else if (ln <= 5'd10) begin
      tmp = (9'h1 << (5'd11 - ln)) - 1;      // 2^(11-ln)-1
      return tmp[7:0];
    end else begin
      return 8'h00;
    end
  endfunction

  // Core functional equivalence
  assert property (@(posedge clk) disable iff (!reset_n)
    line_code == expected_line_code(line_number)
  ) else $error("mouse_painter mapping mismatch: ln=%0d lc=0x%0h exp=0x%0h",
                line_number, line_code, expected_line_code(line_number));

  // Output never X/Z when input is known
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown(line_number) |-> !$isunknown(line_code)
  ) else $error("mouse_painter produced X/Z on known input");

  // Stability: if input stable, output stable
  assert property (@(posedge clk) disable iff (!reset_n)
    $stable(line_number) |-> $stable(line_code)
  ) else $error("mouse_painter output changed without input change");

  // Change-causality: output change implies input change
  assert property (@(posedge clk) disable iff (!reset_n)
    (line_code != $past(line_code)) |-> (line_number != $past(line_number))
  ) else $error("mouse_painter output changed without input change (past)");

  // Shape check: outputs are always (2^k - 1), including 0
  assert property (@(posedge clk) disable iff (!reset_n)
    (line_code & (line_code + 8'h01)) == 8'h00
  ) else $error("mouse_painter line_code not of form 2^k-1: 0x%0h", line_code);

  // Coverage: hit each exact mapping 0..10
  genvar i;
  generate
    for (i = 0; i <= 10; i++) begin : cov_each_code
      cover property (@(posedge clk)
        (line_number == 5'(i)) && (line_code == expected_line_code(5'(i)))
      );
    end
  endgenerate

  // Coverage: default range 11..31 produces 0
  cover property (@(posedge clk)
    (line_number inside {[5'd11:5'd31]}) && (line_code == 8'h00)
  );

endmodule

// Example bind (connect your clock/reset):
// bind mouse_painter mouse_painter_sva u_mouse_painter_sva (.* , .clk(tb_clk), .reset_n(tb_rst_n));