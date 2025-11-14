`ifndef PARC_INT_MUL_VARIABLE_V
`define PARC_INT_MUL_VARIABLE_V

module imuldiv_IntMulVariable
(
  input         clk,
  input         reset,

  input  [31:0] mulreq_msg_a,
  input  [31:0] mulreq_msg_b,
  input         mulreq_val,
  output        mulreq_rdy,

  output [31:0] mulresp_msg_result,
  output        mulresp_val,
  input         mulresp_rdy
);

  wire          sign;
  wire   [31:0] b_data;
  wire          sign_en;
  wire          result_en;
  wire          a_mux_sel;
  wire          b_mux_sel;
  wire    [4:0] op_shamt;
  wire          result_mux_sel;
  wire          add_mux_sel;
  wire          sign_mux_sel;

  wire   [63:0] dpath_out;
  assign mulresp_msg_result = dpath_out[31:0];

  imuldiv_IntMulVariableDpath dpath
  (
    .clk                (clk),
    .reset              (reset),
    .mulreq_msg_a       (mulreq_msg_a),
    .mulreq_msg_b       (mulreq_msg_b),
    .mulresp_msg_result (dpath_out),
    .sign               (sign),
    .b_data             (b_data),
    .sign_en            (sign_en),
    .result_en          (result_en),
    .a_mux_sel          (a_mux_sel),
    .b_mux_sel          (b_mux_sel),
    .op_shamt           (op_shamt),
    .result_mux_sel     (result_mux_sel),
    .add_mux_sel        (add_mux_sel),
    .sign_mux_sel       (sign_mux_sel)
  );

  imuldiv_IntMulVariableCtrl ctrl
  (
    .clk            (clk),
    .reset          (reset),
    .mulreq_val     (mulreq_val),
    .mulreq_rdy     (mulreq_rdy),
    .mulresp_val    (mulresp_val),
    .mulresp_rdy    (mulresp_rdy),
    .sign           (sign),
    .b_data         (b_data),
    .sign_en        (sign_en),
    .result_en      (result_en),
    .a_mux_sel      (a_mux_sel),
    .b_mux_sel      (b_mux_sel),
    .op_shamt       (op_shamt),
    .result_mux_sel (result_mux_sel),
    .add_mux_sel    (add_mux_sel),
    .sign_mux_sel   (sign_mux_sel)
  );

endmodule

module imuldiv_IntMulVariableDpath
(
  input                clk,
  input                reset,

  input  [31:0] mulreq_msg_a,
  input  [31:0] mulreq_msg_b,
  output [63:0] mulresp_msg_result,

  output        sign,
  output [31:0] b_data,

  input         sign_en,
  input         result_en,
  input         a_mux_sel,
  input         b_mux_sel,
  input   [4:0] op_shamt,
  input         result_mux_sel,
  input         add_mux_sel,
  input         sign_mux_sel
);

  localparam op_x     = 1'dx;
  localparam op_load  = 1'd0;
  localparam op_next  = 1'd1;

  localparam add_x    = 1'dx;
  localparam add_old  = 1'd0;
  localparam add_next = 1'd1;

  localparam sign_x   = 1'dx;
  localparam sign_u   = 1'd0;
  localparam sign_s   = 1'd1;

  reg         sign_reg;
  wire [63:0] a_shift_out;
  wire [31:0] b_shift_out;
  wire [63:0] result_mux_out;
  wire [63:0] signed_result_mux_out;

  wire   sign_next = mulreq_msg_a[31] ^ mulreq_msg_b[31];

  assign sign      = sign_reg;

  wire [31:0] unsigned_a
    = ( mulreq_msg_a[31] ) ? ~mulreq_msg_a + 1'b1
    :                         mulreq_msg_a;

  wire [31:0] unsigned_b
    = ( mulreq_msg_b[31] ) ? ~mulreq_msg_b + 1'b1
    :                         mulreq_msg_b;

  wire [63:0] a_mux_out
    = ( a_mux_sel == op_load ) ? { 32'b0, unsigned_a }
    : ( a_mux_sel == op_next ) ? a_shift_out
    :                            64'bx;

  wire [31:0]   b_mux_out
    = ( b_mux_sel == op_load ) ? unsigned_b
    : ( b_mux_sel == op_next ) ? b_shift_out
    :                            32'bx;

  reg [63:0] a_reg;
  reg [31:0] b_reg;
  reg [63:0] result_reg;

  always @ ( posedge clk ) begin
    if ( sign_en ) begin
      sign_reg   <= sign_next;
    end

    if ( result_en ) begin
      result_reg <= result_mux_out;
    end

    a_reg        <= a_mux_out;
    b_reg        <= b_mux_out;
  end

  assign b_data = b_reg;

  assign a_shift_out = a_reg << op_shamt;

  assign b_shift_out = b_reg >> op_shamt;

  wire [63:0] add_out = result_reg + a_reg;

  wire [63:0] add_mux_out
    = ( add_mux_sel == add_old )  ? result_reg
    : ( add_mux_sel == add_next ) ? add_out
    :                               64'bx;

  assign result_mux_out
    = ( result_mux_sel == op_load ) ? 64'b0
    : ( result_mux_sel == op_next ) ? add_mux_out
    :                                 64'bx;

  assign signed_result_mux_out
    = ( sign_mux_sel == sign_u ) ? result_reg
    : ( sign_mux_sel == sign_s ) ? ~result_reg + 1'b1
    :                              64'bx;

  assign mulresp_msg_result = signed_result_mux_out;

endmodule

module imuldiv_IntMulVariableCtrl
(
  input        clk,
  input        reset,

  input        mulreq_val,
  output       mulreq_rdy,

  output       mulresp_val,
  input        mulresp_rdy,

  input        sign,
  input [31:0] b_data,

  output       sign_en,
  output       result_en,
  output       a_mux_sel,
  output       b_mux_sel,
  output [4:0] op_shamt,
  output       result_mux_sel,
  output       add_mux_sel,
  output       sign_mux_sel
);

  localparam STATE_IDLE = 2'd0;
  localparam STATE_CALC = 2'd1;
  localparam STATE_SIGN = 2'd2;

  reg [1:0] state_reg;
  reg [1:0] state_next;

  always @ ( posedge clk ) begin
    if ( reset ) begin
      state_reg <= STATE_IDLE;
    end
    else begin
      state_reg <= state_next;
    end
  end

  wire mulreq_go;
  wire mulresp_go;
  wire is_calc_done;

  always @ ( * ) begin

    state_next = state_reg;

    case ( state_reg )

      STATE_IDLE:
        if ( mulreq_go ) begin
          state_next = STATE_CALC;
        end

      STATE_CALC:
        if ( is_calc_done ) begin
          state_next = STATE_SIGN;
        end

      STATE_SIGN:
        if ( mulresp_go ) begin
          state_next = STATE_IDLE;
        end

    endcase

  end

  localparam n = 1'd0;
  localparam y = 1'd1;

  localparam op_x    = 1'dx;
  localparam op_load = 1'd0;
  localparam op_next = 1'd1;

  localparam cs_size = 7;
  reg [cs_size-1:0] cs;

  always @ ( * ) begin

    cs = 7'b0;

    case ( state_reg )

      STATE_IDLE: cs = { y,     n,      y,   y,     op_load, op_load, op_load };
      STATE_CALC: cs = { n,     n,      n,   y,     op_next, op_next, op_next };
      STATE_SIGN: cs = { n,     y,      n,   n,     op_x,    op_x,    op_x    };

    endcase

  end

  wire b_lsb = b_data[0];

  assign mulreq_rdy     = cs[6];
  assign mulresp_val    = cs[5];
  assign sign_en        = cs[4];
  assign result_en      = cs[3];
  assign a_mux_sel      = cs[2];
  assign b_mux_sel      = cs[1];
  assign result_mux_sel = cs[0];
  assign add_mux_sel    = b_lsb;
  assign sign_mux_sel   = sign;

  wire [31:0] in_bits = b_data >> 1;
  wire        out_val;
  wire [4:0]  out_bits;

  vc_32_5_ReversePriorityEncoder encoder
  (
    .in_bits  (in_bits),
    .out_val  (out_val),
    .out_bits (out_bits)
  );

  assign op_shamt = out_bits + 5'b1;

  assign mulreq_go     = mulreq_val && mulreq_rdy;
  assign mulresp_go    = mulresp_val && mulresp_rdy;

  assign is_calc_done  = ( ( b_data >> 1 ) == 32'b0 );

endmodule

module vc_32_5_ReversePriorityEncoder
(
  input  [31:0] in_bits,
  output        out_val,
  output  [4:0] out_bits
);

  assign out_val = ( in_bits != 32'b0 );

  assign out_bits =
    ( in_bits[ 0] ) ? 5'b00000
  : ( in_bits[ 1] ) ? 5'b00001
  : ( in_bits[ 2] ) ? 5'b00010
  : ( in_bits[ 3] ) ? 5'b00011
  : ( in_bits[ 4] ) ? 5'b00100
  : ( in_bits[ 5] ) ? 5'b00101
  : ( in_bits[ 6] ) ? 5'b00110
  : ( in_bits[ 7] ) ? 5'b00111
  : ( in_bits[ 8] ) ? 5'b01000
  : ( in_bits[ 9] ) ? 5'b01001
  : ( in_bits[10] ) ? 5'b01010
  : ( in_bits[11] ) ? 5'b01011
  : ( in_bits[12] ) ? 5'b01100
  : ( in_bits[13] ) ? 5'b01101
  : ( in_bits[14] ) ? 5'b01110
  : ( in_bits[15] ) ? 5'b01111
  : ( in_bits[16] ) ? 5'b10000
  : ( in_bits[17] ) ? 5'b10001
  : ( in_bits[18] ) ? 5'b10010
  : ( in_bits[19] ) ? 5'b10011
  : ( in_bits[20] ) ? 5'b10100
  : ( in_bits[21] ) ? 5'b10101
  : ( in_bits[22] ) ? 5'b10110
  : ( in_bits[23] ) ? 5'b10111
  : ( in_bits[24] ) ? 5'b11000
  : ( in_bits[25] ) ? 5'b11001
  : ( in_bits[26] ) ? 5'b11010
  : ( in_bits[27] ) ? 5'b11011
  : ( in_bits[28] ) ? 5'b11100
  : ( in_bits[29] ) ? 5'b11101
  : ( in_bits[30] ) ? 5'b11110
  : ( in_bits[31] ) ? 5'b11111
  :                   5'b00000;

endmodule


`endif
