module axis_frame_length_adjust #(
    parameter DATA_WIDTH = 8,
    parameter KEEP_ENABLE = (DATA_WIDTH>8),
    parameter KEEP_WIDTH = (DATA_WIDTH/8),
    parameter ID_ENABLE = 1,
    parameter ID_WIDTH = 8,
    parameter DEST_ENABLE = 1,
    parameter DEST_WIDTH = 8,
    parameter USER_ENABLE = 1,
    parameter USER_WIDTH = 1
)
(
    input clk,
    input rst,
    input [DATA_WIDTH-1:0] s_axis_tdata,
    input [KEEP_WIDTH-1:0] s_axis_tkeep,
    input s_axis_tvalid,
    output reg s_axis_tready,
    input s_axis_tlast,
    input [ID_WIDTH-1:0] s_axis_tid,
    input [DEST_WIDTH-1:0] s_axis_tdest,
    input [USER_WIDTH-1:0] s_axis_tuser,
    output reg [DATA_WIDTH-1:0] m_axis_tdata,
    output reg [KEEP_WIDTH-1:0] m_axis_tkeep,
    output reg m_axis_tvalid,
    input m_axis_tready,
    output reg m_axis_tlast,
    output reg [ID_WIDTH-1:0] m_axis_tid,
    output reg [DEST_WIDTH-1:0] m_axis_tdest,
    output reg [USER_WIDTH-1:0] m_axis_tuser,
    output reg status_valid,
    input status_ready,
    output reg status_frame_pad,
    output reg status_frame_truncate,
    output reg [15:0] status_frame_length,
    output reg [15:0] status_frame_original_length,
    input [15:0] length_min,
    input [15:0] length_max
);

localparam IDLE = 2'b00;
localparam READ_HEADER = 2'b01;
localparam READ_DATA = 2'b10;
localparam WRITE_DATA = 2'b11;

reg [1:0] state = IDLE;
reg [15:0] frame_length = 0;
reg [15:0] frame_original_length = 0;
reg [15:0] frame_counter = 0;
reg [15:0] pad_counter = 0;
reg [15:0] truncate_counter = 0;
reg [DATA_WIDTH-1:0] data_reg = 0;
reg [KEEP_WIDTH-1:0] keep_reg = 0;

always @(posedge clk) begin
    if (rst) begin
        state <= IDLE;
        frame_length <= 0;
        frame_original_length <= 0;
        frame_counter <= 0;
        pad_counter <= 0;
        truncate_counter <= 0;
        m_axis_tvalid <= 0;
        m_axis_tlast <= 0;
        status_valid <= 0;
        status_frame_pad <= 0;
        status_frame_truncate <= 0;
        status_frame_length <= 0;
        status_frame_original_length <= 0;
    end else begin
        case (state)
            IDLE: begin
                if (s_axis_tvalid && m_axis_tready) begin
                    state <= READ_HEADER;
                    frame_length <= 0;
                    frame_original_length <= 0;
                    frame_counter <= 0;
                    pad_counter <= 0;
                    truncate_counter <= 0;
                    m_axis_tvalid <= 1;
                    m_axis_tlast <= 0;
                    m_axis_tid <= s_axis_tid;
                    m_axis_tdest <= s_axis_tdest;
                    m_axis_tuser <= s_axis_tuser;
                    data_reg <= s_axis_tdata;
                    keep_reg <= s_axis_tkeep;
                end else begin
                    m_axis_tvalid <= 0;
                    s_axis_tready <= 1;
                end
            end
            READ_HEADER: begin
                if (s_axis_tvalid && m_axis_tready) begin
                    frame_length <= {s_axis_tdata, 16'b0};
                    frame_original_length <= frame_length;
                    if (frame_length < length_min) begin
                        pad_counter <= length_min - frame_length;
                        frame_length <= length_min;
                        status_frame_pad <= 1;
                    end else if (frame_length > length_max) begin
                        truncate_counter <= frame_length - length_max;
                        frame_length <= length_max;
                        status_frame_truncate <= 1;
                    end
                    status_frame_length <= frame_length;
                    status_frame_original_length <= frame_original_length;
                    m_axis_tdata <= s_axis_tdata;
                    m_axis_tkeep <= s_axis_tkeep;
                    m_axis_tlast <= s_axis_tlast;
                    frame_counter <= 0;
                    state <= READ_DATA;
                end else begin
                    m_axis_tvalid <= 0;
                    s_axis_tready <= 1;
                end
            end
            READ_DATA: begin
                if (s_axis_tvalid && m_axis_tready) begin
                    m_axis_tdata <= s_axis_tdata;
                    m_axis_tkeep <= s_axis_tkeep;
                    m_axis_tlast <= s_axis_tlast;
                    frame_counter <= frame_counter + 1;
                    if (frame_counter == frame_length - 1) begin
                        m_axis_tlast <= 1;
                        state <= WRITE_DATA;
                    end
                end else begin
                    m_axis_tvalid <= 0;
                    s_axis_tready <= 1;
                end
            end
            WRITE_DATA: begin
                if (m_axis_tready && status_ready) begin
                    if (pad_counter > 0) begin
                        m_axis_tdata <= 0;
                        m_axis_tkeep <= {keep_reg, 8'b0};
                        pad_counter <= pad_counter - 1;
                    end else if (truncate_counter > 0) begin
                        truncate_counter <= truncate_counter - 1;
                    end else begin
                        state <= IDLE;
                    end
                    status_valid <= 1;
                end else begin
                    m_axis_tvalid <= 0;
                    s_axis_tready <= 1;
                    status_valid <= 0;
                end
            end
        endcase
    end
end

endmodule