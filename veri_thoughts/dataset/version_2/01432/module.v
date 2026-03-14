module input_output_module(
    input wire CLK,
    output reg [6:0] Q
);

reg [6:0] inputs_reg;
wire [6:0] inputs_delayed;

always @(posedge CLK) begin
    inputs_reg <= Q;
end

assign inputs_delayed[0] = inputs_reg[6];
assign inputs_delayed[1] = inputs_reg[5];
assign inputs_delayed[2] = inputs_reg[4];
assign inputs_delayed[3] = inputs_reg[3];
assign inputs_delayed[4] = inputs_reg[2];
assign inputs_delayed[5] = inputs_reg[1];
assign inputs_delayed[6] = inputs_reg[0];

reg [6:0] delay_counter;
reg [2:0] input_counter;
reg [1:0] state_counter;

always @(posedge CLK) begin
    delay_counter <= delay_counter + 1;
    if (delay_counter == 20) begin
        delay_counter <= 0;
        input_counter <= input_counter + 1;
        if (input_counter == 7) begin
            input_counter <= 0;
            state_counter <= state_counter + 1;
            if (state_counter == 3) begin
                state_counter <= 0;
            end
        end
    end
end

reg [6:0] inputs_pattern_0 = 7'b1000000;
reg [6:0] inputs_pattern_1 = 7'b0111111;
reg [6:0] inputs_pattern_2 = 7'bxxxxxxx;

always @(posedge CLK) begin
    case (state_counter)
        0: Q <= inputs_pattern_0;
        1: Q <= inputs_pattern_1;
        2: Q <= inputs_pattern_2;
    endcase
end

wire Q_delayed;
reg Q_delayed_reg;
assign Q_delayed = Q;

always @(posedge CLK) begin
    Q_delayed_reg <= Q;
end

endmodule