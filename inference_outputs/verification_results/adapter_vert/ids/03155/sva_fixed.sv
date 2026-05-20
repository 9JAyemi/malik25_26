module math_ops_sva (
    input logic add1,
    input logic clk,
    input logic cos,
    input logic one,
    input logic s1,
    input logic s1_out,
    input logic s2,
    input logic s2_out,
    input logic sub5,
    input logic x2,
    input logic x3,
    input logic x6,
    input logic x7
);

property AddOneeotid; @(posedge clk) (cos) == (one) && (s2) |-> (add1) == (cos + one); endproperty
assert property (AddOneeotid);

property ValidXeotid; @(posedge clk) (cos) == (one) && (s2) |-> (x2) == (add1 * s2); endproperty
assert property (ValidXeotid);

property ValidXeotid_2; @(posedge clk) (cos) == (one) && (s2) |-> (x3) == (cos * s1); endproperty
assert property (ValidXeotid_2);

property ValidSumeotid; @(posedge clk) (cos) == (one) && (s2) |-> (s1_out) == (x2 + x3); endproperty
assert property (ValidSumeotid);

property ValidSubeotid; @(posedge clk) (cos) != (one) && (s1) |-> (sub5) == (one - cos); endproperty
assert property (ValidSubeotid);

property ValidXeotid_3; @(posedge clk) (cos) != (one) && (s1) |-> (x6) == (sub5 * s1); endproperty
assert property (ValidXeotid_3);

property ValidXeotid_4; @(posedge clk) (cos) != (one) && (s1) |-> (x7) == (cos * s2); endproperty
assert property (ValidXeotid_4);

property ValidSumeotid_2; @(posedge clk) (cos) != (one) && (s1) |-> (s2_out) == (x6 + x7); endproperty
assert property (ValidSumeotid_2);

endmodule