module pipelined_bitwise_operations_sva (
    input logic and1,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic or1,
    input logic xor1,
    input logic and2,
    input logic and3,
    input logic clk_in_1,
    input logic or2,
    input logic or3,
    input logic xor2,
    input logic xor3
);

property BitwiseAndeotid; @(posedge clk_in_1) ( in1 ) && (  in2 ) |-> ( and1 ) ; endproperty
assert property (BitwiseAndeotid);

property BitwiseOrEeotid; @(posedge clk_in_1) ( in1 ) || (  in2 ) |-> ( or1 ) ; endproperty
assert property (BitwiseOrEeotid);

property BitwiseXorEeotid; @(posedge clk_in_1) ( in1 ) != (  in2 ) |-> ( xor1 ) ; endproperty
assert property (BitwiseXorEeotid);

property AndSynceotid; @(posedge clk_in_1) ( in1 ) && (  in2 ) && (  in3 ) |-> ( and2 ) ; endproperty
assert property (AndSynceotid);

property OrSynceotid; @(posedge clk_in_1) ( in1 ) || (  in2 ) || (  in3 ) |-> ( or2 ) ; endproperty
assert property (OrSynceotid);

property XorSynceotid; @(posedge clk_in_1) ( in1 ) != (  in2 ) && (  in3 ) |-> ( xor2 ) ; endproperty
assert property (XorSynceotid);

property AndSynceotid_2; @(posedge clk_in_1) ( in1 ) && (  in2 ) && (  in3 ) && (  in4 ) |-> ( and3 ) ; endproperty
assert property (AndSynceotid_2);

property OrSynceotid_2; @(posedge clk_in_1) ( in1 ) || (  in2 ) || (  in3 ) || (  in4 ) |-> ( or3 ) ; endproperty
assert property (OrSynceotid_2);

property XorSynceotid_2; @(posedge clk_in_1) ( in1 ) != (  in2 ) && (  in3 ) && (  in4 ) |-> ( xor3 ) ; endproperty
assert property (XorSynceotid_2);

endmodule