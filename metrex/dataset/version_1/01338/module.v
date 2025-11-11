
module sequence_detector (
    input clk,
    input reset,
    input [35:0] in,
    output [3:0] sequence_detected,
    output [31:0] change_detection
);

    reg [35:0] shift_reg;
    reg [3:0] sequence_detected_reg;
    reg [31:0] change_detection_reg;
    wire [31:0] change_detection_output;

    always @(posedge clk) begin
        if (reset) begin
            shift_reg <= 36'b0;
            sequence_detected_reg <= 4'b0;
            change_detection_reg <= 32'b0;
        end else begin
            shift_reg <= {shift_reg[34:0], in};
            if (shift_reg[35:32] == 4'b1010) begin
                sequence_detected_reg <= 4'b1010;
            end else begin
                sequence_detected_reg <= 4'b0;
            end
            change_detection_reg <= change_detection_output;
        end
    end

    assign change_detection_output = ({32'b0, sequence_detected_reg} & (in ^ shift_reg[35:2]));

    assign sequence_detected = sequence_detected_reg;
    assign change_detection = change_detection_reg;

endmodule
module combined_module (
    input clk,
    input reset,
    input [35:0] in,
    output [31:0] out
);

    wire [3:0] sequence_detected;
    wire [31:0] change_detection;

    sequence_detector detector (
        .clk(clk),
        .reset(reset),
        .in(in),
        .sequence_detected(sequence_detected),
        .change_detection(change_detection)
    );

    assign out = (in ^ change_detection) | ({32'b0, sequence_detected} << 28);

endmodule