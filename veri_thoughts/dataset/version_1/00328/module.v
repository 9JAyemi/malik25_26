module priority_encoder (
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] priority_output
);

    assign priority_output = (in1 > in2) ? in1 : in2;

endmodule

module final_output_generator (
    input [3:0] in1,
    input [3:0] in2,
    output reg [3:0] final_output
);

    wire [3:0] priority_output;
    priority_encoder encoder(in1, in2, priority_output);

    always @* begin
        case (priority_output)
            4'b0001: final_output = in1;
            4'b0010: final_output = in2;
            4'b0100: final_output = {in1[3:1], in2[0]};
            4'b1000: final_output = {in2[3:1], in1[0]};
            default: final_output = 4'b0000;
        endcase
    end

endmodule