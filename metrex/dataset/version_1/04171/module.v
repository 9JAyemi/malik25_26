
module wire_connection (
    input [2:0] data_in1,
    input [2:0] data_in2,
    input [2:0] data_in3,
    output [3:0] data_out
);

assign data_out = {data_in3, data_in2, data_in1};

endmodule

module priority_encoder (
    input [3:0] data_in,
    output reg [2:0] index
);

integer i;

always @(*) begin
    index = 0;
    for (i = 0; i < 4; i = i + 1) begin
        if (data_in[i]) begin
            index = i;
        end
    end
end

endmodule

module voting_circuit (
    input clk,
    input reset,
    input [2:0] data_in1,
    input [2:0] data_in2,
    input [2:0] data_in3,
    output reg [2:0] final_output
);

wire [3:0] wire_out;
wire [2:0] encoder_out;

wire_connection wire_conn(
    .data_in1(data_in1),
    .data_in2(data_in2),
    .data_in3(data_in3),
    .data_out(wire_out)
);

priority_encoder priority_enc(
    .data_in(wire_out),
    .index(encoder_out)
);

always @(posedge clk) begin
    if (reset) begin
        final_output <= 0;
    end
    else begin
        final_output <= {3{1'b0}};
        case (encoder_out)
            0: final_output <= data_in1;
            1: final_output <= data_in2;
            2: final_output <= data_in3;
        endcase
    end
end

endmodule
