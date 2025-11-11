module top_module (
    input [3:0] A,
    input [3:0] B,
    output eq,
    output gt,
    input C,
    input [3:0] D,
    output [3:0] final_output
);

    assign eq = (A == B); 
    assign gt = (A > B); 


    wire [3:0] shifted_value;
    assign shifted_value = (C == 0) ? (A << D[1:0]) : (A >> D[1:0]); // Limit shift to meaningful range


    assign final_output = eq ? shifted_value : 4'b0000;

endmodule
