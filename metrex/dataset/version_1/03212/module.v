module uart_rx(
    input             clk,
    input             rst,
    input             RxD,              input             uart_tick_16x,    output reg [7:0]  RxD_data = 0,     output            ready             );

    localparam [3:0] IDLE=0;        localparam [3:0] START=1;       localparam [3:0] BIT_0=2;       localparam [3:0] BIT_1=3;       localparam [3:0] BIT_2=4;       localparam [3:0] BIT_3=5;       localparam [3:0] BIT_4=6;       localparam [3:0] BIT_5=7;       localparam [3:0] BIT_6=8;       localparam [3:0] BIT_7=9;       localparam [3:0] STOP=10;       reg [3:0] state       = IDLE;
    reg       clk_lock    = 0;
    reg [3:0] bit_spacing = 4'b1110;   wire capture;
    wire next_bit;

    assign capture  = (uart_tick_16x & next_bit & (state!=IDLE) & (state!=STOP));
    assign next_bit = (bit_spacing == 4'b1111);


    reg [1:0] RxD_sync = 2'b11; always @(posedge clk) begin
        RxD_sync <= (uart_tick_16x) ? {RxD_sync[0], RxD} : RxD_sync;
    end

    reg [1:0] RxD_cnt = 0;
    reg RxD_bit       = 1; always @(posedge clk) begin
        if (uart_tick_16x) begin
            case (RxD_sync[1])
                0:  RxD_cnt <= (RxD_cnt == 2'b11) ? RxD_cnt : RxD_cnt + 2'b1;
                1:  RxD_cnt <= (RxD_cnt == 2'b00) ? RxD_cnt : RxD_cnt - 2'b1;
            endcase
            RxD_bit <= (RxD_cnt == 2'b11) ? 1'b0 : ((RxD_cnt == 2'b00) ? 1'b1 : RxD_bit);
        end
        else begin
            RxD_cnt <= RxD_cnt;
            RxD_bit <= RxD_bit;
        end
    end

    always @(posedge clk) begin
       if (uart_tick_16x) begin
            if (~clk_lock)
                clk_lock <= ~RxD_bit; else
                clk_lock <= ((state == IDLE) && (RxD_bit == 1'b1)) ? 1'b0 : clk_lock;
            bit_spacing <= (clk_lock) ? bit_spacing + 4'b1 : 4'b1110;
       end
       else begin
            clk_lock    <= clk_lock;
            bit_spacing <= bit_spacing;
       end
    end

    always @(posedge clk) begin
        if (rst)
            state <= IDLE;
        else if (uart_tick_16x) begin
            case (state)
                IDLE:   state <= (next_bit & (RxD_bit == 1'b0)) ? BIT_0 : IDLE;  BIT_0:  state <= (next_bit) ? BIT_1 : BIT_0;
                BIT_1:  state <= (next_bit) ? BIT_2 : BIT_1;
                BIT_2:  state <= (next_bit) ? BIT_3 : BIT_2;
                BIT_3:  state <= (next_bit) ? BIT_4 : BIT_3;
                BIT_4:  state <= (next_bit) ? BIT_5 : BIT_4;
                BIT_5:  state <= (next_bit) ? BIT_6 : BIT_5;
                BIT_6:  state <= (next_bit) ? BIT_7 : BIT_6;
                BIT_7:  state <= (next_bit) ? STOP  : BIT_7;
                STOP:   state <= (next_bit) ? IDLE  : STOP;
                default: state <= 4'bxxxx;
            endcase
        end
        else state <= state;
    end

    always @(posedge clk) begin
        RxD_data <= (capture) ? {RxD_bit, RxD_data[7:1]} : RxD_data[7:0];
    end

    assign ready = (uart_tick_16x & next_bit & (state==STOP));
endmodule
