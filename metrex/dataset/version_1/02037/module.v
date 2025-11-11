
module altera_up_av_config_auto_init_ltm (
    // Inputs
    clk,
    rom_address,

    // Outputs
    rom_data
);




// Inputs
input           clk;
input           [4:0]   rom_address;

// Outputs
output      [23:0]  rom_data;



// States
localparam [4:0] STATE_0 = 5'h0;
localparam [4:0] STATE_1 = 5'h1;
localparam [4:0] STATE_2 = 5'h2;
localparam [4:0] STATE_3 = 5'h3;
localparam [4:0] STATE_4 = 5'h4;
localparam [4:0] STATE_5 = 5'h5;
localparam [4:0] STATE_6 = 5'h6;
localparam [4:0] STATE_7 = 5'h7;
localparam [4:0] STATE_8 = 5'h8;
localparam [4:0] STATE_9 = 5'h9;
localparam [4:0] STATE_10 = 5'hA;
localparam [4:0] STATE_11 = 5'hB;
localparam [4:0] STATE_12 = 5'hC;
localparam [4:0] STATE_13 = 5'hD;
localparam [4:0] STATE_14 = 5'hE;
localparam [4:0] STATE_15 = 5'hF;
localparam [4:0] STATE_16 = 5'h10;
localparam [4:0] STATE_17 = 5'h11;
localparam [4:0] STATE_18 = 5'h12;
localparam [4:0] STATE_19 = 5'h13;


// Internal Wires
reg         [23:0] data;

// State Machine Registers
reg         [4:0]   state_reg;
reg         [4:0]   next_state;



always @(*) begin
    case (state_reg)
        STATE_0 : next_state = (rom_address == 5'h0) ? STATE_0 : STATE_1;
        STATE_1 : next_state = (rom_address == 5'h1) ? STATE_1 : STATE_2;
        STATE_2 : next_state = (rom_address == 5'h2) ? STATE_2 : STATE_3;
        STATE_3 : next_state = (rom_address == 5'h3) ? STATE_3 : STATE_4;
        STATE_4 : next_state = (rom_address == 5'h4) ? STATE_4 : STATE_5;
        STATE_5 : next_state = (rom_address == 5'h5) ? STATE_5 : STATE_6;
        STATE_6 : next_state = (rom_address == 5'h6) ? STATE_6 : STATE_7;
        STATE_7 : next_state = (rom_address == 5'h7) ? STATE_7 : STATE_8;
        STATE_8 : next_state = (rom_address == 5'h8) ? STATE_8 : STATE_9;
        STATE_9 : next_state = (rom_address == 5'h9) ? STATE_9 : STATE_10;
        STATE_10 : next_state = (rom_address == 5'hA) ? STATE_10 : STATE_11;
        STATE_11 : next_state = (rom_address == 5'hB) ? STATE_11 : STATE_12;
        STATE_12 : next_state = (rom_address == 5'hC) ? STATE_12 : STATE_13;
        STATE_13 : next_state = (rom_address == 5'hD) ? STATE_13 : STATE_14;
        STATE_14 : next_state = (rom_address == 5'hE) ? STATE_14 : STATE_15;
        STATE_15 : next_state = (rom_address == 5'hF) ? STATE_15 : STATE_16;
        STATE_16 : next_state = (rom_address == 5'h10) ? STATE_16 : STATE_17;
        STATE_17 : next_state = (rom_address == 5'h11) ? STATE_17 : STATE_18;
        STATE_18 : next_state = (rom_address == 5'h12) ? STATE_18 : STATE_19;
        STATE_19 : next_state = (rom_address == 5'h13) ? STATE_19 : STATE_0;
        default : next_state = STATE_0;
    endcase
end



// State machine
always @(posedge clk) begin
    state_reg <= next_state;
end



// Output Assignments
assign rom_data = {data[13:8], 2'h0, data[7:0]};

// Internal Assignments
always @(*) begin
    case (state_reg)
        STATE_0 : data <= {6'h02, 8'h07};
        STATE_1 : data <= {6'h03, 8'hDF};
        STATE_2 : data <= {6'h04, 8'h17};
        STATE_3 : data <= {6'h11, 8'h00};
        STATE_4 : data <= {6'h12, 8'h5B};
        STATE_5 : data <= {6'h13, 8'hFF};
        STATE_6 : data <= {6'h14, 8'h00};
        STATE_7 : data <= {6'h15, 8'h20};
        STATE_8 : data <= {6'h16, 8'h40};
        STATE_9 : data <= {6'h17, 8'h80};
        STATE_10 : data <= {6'h18, 8'h00};
        STATE_11 : data <= {6'h19, 8'h80};
        STATE_12 : data <= {6'h1A, 8'h00};
        STATE_13 : data <= {6'h1B, 8'h00};
        STATE_14 : data <= {6'h1C, 8'h80};
        STATE_15 : data <= {6'h1D, 8'hC0};
        STATE_16 : data <= {6'h1E, 8'hE0};
        STATE_17 : data <= {6'h1F, 8'hFF};
        STATE_18 : data <= {6'h20, 8'hD2};
        STATE_19 : data <= {6'h21, 8'hD2};
        default : data <= 24'h000000;
    endcase
end



endmodule