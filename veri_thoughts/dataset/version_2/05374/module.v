
module top_module(
    input clk,
    input areset,  // async active-high reset to zero
    input load,
    input ena,
    input [3:0] data1, // input for shift register 1
    input [3:0] data2, // input for shift register 2
    output reg [3:0] q1, // output from shift register 1
    output reg [3:0] q2, // output from shift register 2
    output [3:0] out // output from functional module
);

reg [3:0] sr1_out, sr2_out;

always @(posedge clk or posedge areset) begin
    if (areset) begin
        q1 <= 4'b0;
        q2 <= 4'b0;
        sr1_out <= 4'b0;
        sr2_out <= 4'b0;
    end else begin
        if (load) begin
            q1 <= data1;
            q2 <= data2;
            sr1_out <= data1;
            sr2_out <= data2;
        end else if (ena) begin
            q1 <= {q1[2:0], 1'b0};
            q2 <= {q2[2:0], 1'b0};
            sr1_out <= {sr1_out[2:0], ena};
            sr2_out <= {sr2_out[2:0], ena};
        end
    end
end

assign out = sr1_out ^ sr2_out;

endmodule
