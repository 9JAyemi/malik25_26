


module fg_packet_gen #(
    parameter DEST_WIDTH = 8,
    parameter DATA_WIDTH = 64,
    parameter KEEP_WIDTH = (DATA_WIDTH/8)
)
(
    input  wire                   clk,
    input  wire                   rst,

    
    input  wire                   input_bd_valid,
    output wire                   input_bd_ready,
    input  wire [DEST_WIDTH-1:0]  input_bd_dest,
    input  wire [31:0]            input_bd_burst_len,

    
    output wire                   output_hdr_valid,
    input  wire                   output_hdr_ready,
    output wire [DEST_WIDTH-1:0]  output_hdr_dest,
    output wire [15:0]            output_hdr_len,
    output wire [DATA_WIDTH-1:0]  output_payload_tdata,
    output wire [KEEP_WIDTH-1:0]  output_payload_tkeep,
    output wire                   output_payload_tvalid,
    input  wire                   output_payload_tready,
    output wire                   output_payload_tlast,
    output wire                   output_payload_tuser,

    
    output wire busy,

    
    input  wire [15:0] payload_mtu
);

localparam [1:0]
    STATE_IDLE = 2'd0,
    STATE_BURST = 2'd1,
    STATE_FRAME = 2'd2;

reg [1:0] state_reg = STATE_IDLE, state_next;

reg [31:0] burst_len_reg = 0, burst_len_next;
reg [15:0] frame_len_reg = 0, frame_len_next;

reg input_bd_ready_reg = 0, input_bd_ready_next;

reg output_hdr_valid_reg = 0, output_hdr_valid_next;
reg [DEST_WIDTH-1:0] output_hdr_dest_reg = 0, output_hdr_dest_next;
reg [15:0] output_hdr_len_reg = 0, output_hdr_len_next;

reg busy_reg = 0;

reg [DATA_WIDTH-1:0] output_payload_tdata_int;
reg [KEEP_WIDTH-1:0] output_payload_tkeep_int;
reg                  output_payload_tvalid_int;
reg                  output_payload_tready_int = 0;
reg                  output_payload_tlast_int;
reg                  output_payload_tuser_int;
wire                 output_payload_tready_int_early;

assign input_bd_ready = input_bd_ready_reg;

assign output_hdr_valid = output_hdr_valid_reg;
assign output_hdr_dest = output_hdr_dest_reg;
assign output_hdr_len = output_hdr_len_reg;

assign busy = busy_reg;

always @* begin
    state_next = 0;

    burst_len_next = burst_len_reg;
    frame_len_next = frame_len_reg;

    input_bd_ready_next = 0;

    output_hdr_valid_next = output_hdr_valid_reg & ~output_hdr_ready;
    output_hdr_dest_next = output_hdr_dest_reg;
    output_hdr_len_next = output_hdr_len_reg;

    output_payload_tdata_int = 0;
    output_payload_tkeep_int = 0;
    output_payload_tvalid_int = 0;
    output_payload_tlast_int = 0;
    output_payload_tuser_int = 0;

    case (state_reg)
        STATE_IDLE: begin
            input_bd_ready_next = 1;

            if (input_bd_ready & input_bd_valid) begin
                output_hdr_dest_next = input_bd_dest;
                burst_len_next = input_bd_burst_len;

                state_next = STATE_BURST;
            end else begin
                state_next = STATE_IDLE;
            end
        end
        STATE_BURST: begin
            if (~output_hdr_valid_reg) begin
                if (burst_len_reg > payload_mtu) begin
                    frame_len_next = payload_mtu;
                    burst_len_next = burst_len_reg - payload_mtu;
                    output_hdr_valid_next = 1;
                    output_hdr_len_next = payload_mtu;
                end else begin
                    frame_len_next = burst_len_reg;
                    burst_len_next = 0;
                    output_hdr_valid_next = 1;
                    output_hdr_len_next = burst_len_reg;
                end

                state_next = STATE_FRAME;
            end else begin
                state_next = STATE_BURST;
            end
        end
        STATE_FRAME: begin
            if (output_payload_tready_int) begin
                if (frame_len_reg > KEEP_WIDTH) begin
                    frame_len_next = frame_len_reg - KEEP_WIDTH;
                    output_payload_tkeep_int = {KEEP_WIDTH{1'b1}};
                    output_payload_tvalid_int = 1;
                    state_next = STATE_FRAME;
                end else begin
                    frame_len_next = 0;
                    output_payload_tkeep_int = {KEEP_WIDTH{1'b1}} >> (KEEP_WIDTH - frame_len_reg);
                    output_payload_tvalid_int = 1;
                    output_payload_tlast_int = 1;
                    if (burst_len_reg > 0) begin
                        state_next = STATE_BURST;
                    end else begin
                        state_next = STATE_IDLE;
                    end
                end
            end else begin
                state_next = STATE_FRAME;
            end
        end
    endcase
end

always @(posedge clk or posedge rst) begin
    if (rst) begin
        state_reg <= STATE_IDLE;
        burst_len_reg <= 0;
        frame_len_reg <= 0;
        input_bd_ready_reg <= 0;
        output_hdr_valid_reg <= 0;
        output_hdr_dest_reg <= 0;
        output_hdr_len_reg <= 0;
        busy_reg <= 0;
    end else begin
        state_reg <= state_next;
        burst_len_reg <= burst_len_next;
        frame_len_reg <= frame_len_next;
        input_bd_ready_reg <= input_bd_ready_next;
        output_hdr_valid_reg <= output_hdr_valid_next;
        output_hdr_dest_reg <= output_hdr_dest_next;
        output_hdr_len_reg <= output_hdr_len_next;
        busy_reg <= state_next != STATE_IDLE;
    end
end

reg [DATA_WIDTH-1:0] output_payload_tdata_reg = 0;
reg [KEEP_WIDTH-1:0] output_payload_tkeep_reg = 0;
reg                  output_payload_tvalid_reg = 0;
reg                  output_payload_tlast_reg = 0;
reg                  output_payload_tuser_reg = 0;

reg [DATA_WIDTH-1:0] temp_payload_tdata_reg = 0;
reg [KEEP_WIDTH-1:0] temp_payload_tkeep_reg = 0;
reg                  temp_payload_tvalid_reg = 0;
reg                  temp_payload_tlast_reg = 0;
reg                  temp_payload_tuser_reg = 0;

assign output_payload_tdata = output_payload_tdata_reg;
assign output_payload_tkeep = output_payload_tkeep_reg;
assign output_payload_tvalid = output_payload_tvalid_reg;
assign output_payload_tlast = output_payload_tlast_reg;
assign output_payload_tuser = output_payload_tuser_reg;

assign output_payload_tready_int_early = output_payload_tready | (~temp_payload_tvalid_reg & ~output_payload_tvalid_reg) | (~temp_payload_tvalid_reg & ~output_payload_tvalid_int);

always @(posedge clk or posedge rst) begin
    if (rst) begin
        output_payload_tdata_reg <= 0;
        output_payload_tkeep_reg <= 0;
        output_payload_tvalid_reg <= 0;
        output_payload_tlast_reg <= 0;
        output_payload_tuser_reg <= 0;
        output_payload_tready_int <= 0;
        temp_payload_tdata_reg <= 0;
        temp_payload_tkeep_reg <= 0;
        temp_payload_tvalid_reg <= 0;
        temp_payload_tlast_reg <= 0;
        temp_payload_tuser_reg <= 0;
    end else begin
        output_payload_tready_int <= output_payload_tready_int_early;

        if (output_payload_tready_int) begin
            if (output_payload_tready | ~output_payload_tvalid_reg) begin
                output_payload_tdata_reg <= output_payload_tdata_int;
                output_payload_tkeep_reg <= output_payload_tkeep_int;
                output_payload_tvalid_reg <= output_payload_tvalid_int;
                output_payload_tlast_reg <= output_payload_tlast_int;
                output_payload_tuser_reg <= output_payload_tuser_int;
            end else begin
                temp_payload_tdata_reg <= output_payload_tdata_int;
                temp_payload_tkeep_reg <= output_payload_tkeep_int;
                temp_payload_tvalid_reg <= output_payload_tvalid_int;
                temp_payload_tlast_reg <= output_payload_tlast_int;
                temp_payload_tuser_reg <= output_payload_tuser_int;
            end
        end else if (output_payload_tready) begin
            output_payload_tdata_reg <= temp_payload_tdata_reg;
            output_payload_tkeep_reg <= temp_payload_tkeep_reg;
            output_payload_tvalid_reg <= temp_payload_tvalid_reg;
            output_payload_tlast_reg <= temp_payload_tlast_reg;
            output_payload_tuser_reg <= temp_payload_tuser_reg;
            temp_payload_tdata_reg <= 0;
            temp_payload_tkeep_reg <= 0;
            temp_payload_tvalid_reg <= 0;
            temp_payload_tlast_reg <= 0;
            temp_payload_tuser_reg <= 0;
        end
    end
end

endmodule
