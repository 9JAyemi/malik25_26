module top_module_sva (
    input wire [3:0] in1,
    input wire [3:0] in2,
    output wire [3:0] out,
    output wire [3:0] max_out
);
    // No clock or reset signals are present in the RTL

    // Combinational logic: sum is calculated and assigned to out
    // The sum is stored in the variable 'sum'
    wire [3:0] sum;
    assign sum = in1 + in2;

    // Combinational logic: max_value is calculated and assigned to max_out
    // The maximum value is stored in the variable 'max_value'
    wire [3:0] max_value;
    assign max_value = (out > sum) ? out : sum;

    // Assigning the sum to the out port
    assign out = sum;

    // Assigning the maximum value to the max_out port
    assign max_out = max_value;

    // No sequential logic or clocked assertions are needed for this combinational design
endmodule