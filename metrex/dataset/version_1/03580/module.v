
module edge_detect_mux (
    input clk,
    input rst_n,
    input a, b, c,
    input select,
    output reg rise,
    output reg fall,
    output reg w,
    output reg x,
    output reg y,
    output reg z
);

    // State definitions
    localparam [1:0]
        IDLE = 2'b00,
        RISING_EDGE = 2'b01,
        FALLING_EDGE = 2'b10,
        MUX_SELECT = 2'b11;

    // State register and next state logic
    reg [1:0] state, next_state;
    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end

    // Output register and combinational logic
    reg [2:0] mux_out;
    always @(*) begin
        case (select)
            0: mux_out = {a, 2'b00};
            1: mux_out = {b, 2'b00};
            2: mux_out = {c, 2'b00};
            default: mux_out = 3'b000; // Added a default case to break the logic loop
        endcase
        w = select;
        x = mux_out[2];
        y = mux_out[1];
        z = mux_out[0];
    end

    // State machine
    always @(*) begin
        case (state)
            IDLE: begin
                rise <= 1'b0;
                fall <= 1'b0;
                next_state = RISING_EDGE;
            end
            RISING_EDGE: begin
                rise <= a; // Fixed the edge detection logic for the rising edge
                fall <= 1'b0;
                next_state = FALLING_EDGE;
            end
            FALLING_EDGE: begin
                rise <= 1'b0;
                fall <= ~a; // Fixed the edge detection logic for the falling edge
                next_state = MUX_SELECT;
            end
            MUX_SELECT: begin
                rise <= 1'b0;
                fall <= 1'b0;
                next_state = IDLE;
            end
        endcase
    end

endmodule