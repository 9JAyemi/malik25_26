// SVA for calculator
module calculator_sva (
  input logic                 clk,
  input logic                 rst,
  input logic signed   [7:0]  a,
  input logic signed   [7:0]  b,
  input logic         [2:0]   op,
  input logic signed   [7:0]  result,
  input logic                 of
);

  localparam signed [7:0] MIN = 8'sh80;   // -128
  localparam signed [7:0] MAX = 8'sd127;  //  127

  function automatic bit add_of(input signed [7:0] a, b);
    int signed ai = a, bi = b;
    return ((bi > 0 && ai > (32'sd127 - bi)) || (bi < 0 && ai < (32'sd-128 - bi)));
  endfunction

  function automatic bit sub_of(input signed [7:0] a, b);
    int signed ai = a, bi = b;
    return ((bi < 0 && ai > (32'sd127 + bi)) || (bi > 0 && ai < (32'sd-128 + bi)));
  endfunction

  function automatic bit mul_of(input signed [7:0] a, b);
    return ((a == MIN && b == -1) || (b == MIN && a == -1));
  endfunction

  function automatic bit div_of(input signed [7:0] a, b);
    return (b == 0);
  endfunction

  // Reset behavior
  assert property (@(posedge clk) rst |-> (result == 0 && of == 0));

  // Legal op only; illegal ops must hold outputs stable
  assert property (@(posedge clk) disable iff (rst)
    (op inside {3'b000,3'b001,3'b010,3'b011})
  );

  assert property (@(posedge clk) disable iff (rst)
    (!(op inside {3'b000,3'b001,3'b010,3'b011})) |-> ($stable(result) && $stable(of))
  );

  // Addition
  assert property (@(posedge clk) disable iff (rst)
    (op == 3'b000) |-> (of == add_of(a,b) && result == (a + b))
  );

  // Subtraction
  assert property (@(posedge clk) disable iff (rst)
    (op == 3'b001) |-> (of == sub_of(a,b) && result == (a - b))
  );

  // Multiplication
  assert property (@(posedge clk) disable iff (rst)
    (op == 3'b010) |-> (of == mul_of(a,b) && result == (a * b))
  );

  // Division (explicitly check div-by-zero X result)
  assert property (@(posedge clk) disable iff (rst)
    (op == 3'b011 && b != 0) |-> (of == 0 && result == (a / b))
  );

  assert property (@(posedge clk) disable iff (rst)
    (op == 3'b011 && b == 0) |-> (of == 1 && $isunknown(result))
  );

  // Coverage
  cover property (@(posedge clk) rst);
  cover property (@(posedge clk) disable iff (rst) (op == 3'b000));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b001));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b010));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b011));

  cover property (@(posedge clk) disable iff (rst) (op == 3'b000 && add_of(a,b)));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b000 && !add_of(a,b)));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b001 && sub_of(a,b)));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b001 && !sub_of(a,b)));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b010 && mul_of(a,b)));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b010 && !mul_of(a,b)));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b011 && b == 0));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b011 && b != 0));

  cover property (@(posedge clk) disable iff (rst) (op == 3'b010 && a == MIN && b == -1));
  cover property (@(posedge clk) disable iff (rst) (op == 3'b010 && b == MIN && a == -1));

endmodule

bind calculator calculator_sva i_calculator_sva(.*);