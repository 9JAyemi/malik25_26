


 
module generic_baseblocks_v2_1_mux_enc #
  (
   parameter         C_FAMILY                       = "rtl",
                       parameter integer C_RATIO                        = 4,
                       parameter integer C_SEL_WIDTH                    = 2,
                       parameter integer C_DATA_WIDTH                   = 1
                       )
  (
   input  wire [C_SEL_WIDTH-1:0]                    S,
   input  wire [C_RATIO*C_DATA_WIDTH-1:0]           A,
   output wire [C_DATA_WIDTH-1:0]                   O,
   input  wire                                      OE
   );
  
  wire [C_DATA_WIDTH-1:0] o_i;
  genvar bit_cnt;
  
  function [C_DATA_WIDTH-1:0] f_mux
    (
     input [C_SEL_WIDTH-1:0] s,
     input [C_RATIO*C_DATA_WIDTH-1:0] a
     );
    integer i;
    reg [C_RATIO*C_DATA_WIDTH-1:0] carry;
    begin
      carry[C_DATA_WIDTH-1:0] = {C_DATA_WIDTH{(s==0)?1'b1:1'b0}} & a[C_DATA_WIDTH-1:0];
      for (i=1;i<C_RATIO;i=i+1) begin : gen_carrychain_enc
        carry[i*C_DATA_WIDTH +: C_DATA_WIDTH] = 
          carry[(i-1)*C_DATA_WIDTH +: C_DATA_WIDTH] |
          ({C_DATA_WIDTH{(s==i)?1'b1:1'b0}} & a[i*C_DATA_WIDTH +: C_DATA_WIDTH]);
      end
      f_mux = carry[C_DATA_WIDTH*C_RATIO-1:C_DATA_WIDTH*(C_RATIO-1)];
    end
  endfunction
  
  function [C_DATA_WIDTH-1:0] f_mux4
    (
     input [1:0] s,
     input [4*C_DATA_WIDTH-1:0] a
     );
    integer i;
    reg [4*C_DATA_WIDTH-1:0] carry;
    begin
      carry[C_DATA_WIDTH-1:0] = {C_DATA_WIDTH{(s==0)?1'b1:1'b0}} & a[C_DATA_WIDTH-1:0];
      for (i=1;i<4;i=i+1) begin : gen_carrychain_enc
        carry[i*C_DATA_WIDTH +: C_DATA_WIDTH] = 
          carry[(i-1)*C_DATA_WIDTH +: C_DATA_WIDTH] |
          ({C_DATA_WIDTH{(s==i)?1'b1:1'b0}} & a[i*C_DATA_WIDTH +: C_DATA_WIDTH]);
      end
      f_mux4 = carry[C_DATA_WIDTH*4-1:C_DATA_WIDTH*3];
    end
  endfunction
  
  assign O = o_i & {C_DATA_WIDTH{OE}};  generate
    if ( C_RATIO < 2 ) begin : gen_bypass
      assign o_i = A;
    end else if ( C_FAMILY == "rtl" || C_RATIO < 5 ) begin : gen_rtl
      assign o_i = f_mux(S, A);
      
    end else begin : gen_fpga
      wire [C_DATA_WIDTH-1:0] l;
      wire [C_DATA_WIDTH-1:0] h;
      wire [C_DATA_WIDTH-1:0] ll;
      wire [C_DATA_WIDTH-1:0] lh;
      wire [C_DATA_WIDTH-1:0] hl;
      wire [C_DATA_WIDTH-1:0] hh;
      
      case (C_RATIO)
        1, 5, 9, 13: 
          assign hh = A[(C_RATIO-1)*C_DATA_WIDTH +: C_DATA_WIDTH];
        2, 6, 10, 14:
          assign hh = S[0] ? 
            A[(C_RATIO-1)*C_DATA_WIDTH +: C_DATA_WIDTH] :
            A[(C_RATIO-2)*C_DATA_WIDTH +: C_DATA_WIDTH] ;
        3, 7, 11, 15:
          assign hh = S[1] ? 
            A[(C_RATIO-1)*C_DATA_WIDTH +: C_DATA_WIDTH] :
            (S[0] ? 
              A[(C_RATIO-2)*C_DATA_WIDTH +: C_DATA_WIDTH] :
              A[(C_RATIO-3)*C_DATA_WIDTH +: C_DATA_WIDTH] );
        4, 8, 12, 16:
          assign hh = S[1] ? 
            (S[0] ? 
              A[(C_RATIO-1)*C_DATA_WIDTH +: C_DATA_WIDTH] :
              A[(C_RATIO-2)*C_DATA_WIDTH +: C_DATA_WIDTH] ) :
            (S[0] ? 
              A[(C_RATIO-3)*C_DATA_WIDTH +: C_DATA_WIDTH] :
              A[(C_RATIO-4)*C_DATA_WIDTH +: C_DATA_WIDTH] );
        17:
          assign hh = S[1] ? 
            (S[0] ? 
              A[15*C_DATA_WIDTH +: C_DATA_WIDTH] :
              A[14*C_DATA_WIDTH +: C_DATA_WIDTH] ) :
            (S[0] ? 
              A[13*C_DATA_WIDTH +: C_DATA_WIDTH] :
              A[12*C_DATA_WIDTH +: C_DATA_WIDTH] );
        default:
          assign hh = 0; 
      endcase

      case (C_RATIO)
        5, 6, 7, 8: begin
          assign l = f_mux4(S[1:0], A[0 +: 4*C_DATA_WIDTH]);
          for (bit_cnt = 0; bit_cnt < C_DATA_WIDTH ; bit_cnt = bit_cnt + 1) begin : gen_mux_5_8
            MUXF7 mux_s2_inst 
            (
             .I0  (l[bit_cnt]),
             .I1  (hh[bit_cnt]),
             .S   (S[2]),
             .O   (o_i[bit_cnt])
            ); 
          end
        end
          
        9, 10, 11, 12: begin
          assign ll = f_mux4(S[1:0], A[0 +: 4*C_DATA_WIDTH]);
          assign lh = f_mux4(S[1:0], A[4*C_DATA_WIDTH +: 4*C_DATA_WIDTH]);
          for (bit_cnt = 0; bit_cnt < C_DATA_WIDTH ; bit_cnt = bit_cnt + 1) begin : gen_mux_9_12
            MUXF7 muxf_s2_low_inst 
            (
             .I0  (ll[bit_cnt]),
             .I1  (lh[bit_cnt]),
             .S   (S[2]),
             .O   (l[bit_cnt])
            ); 
            MUXF8 muxf_s3_inst 
            (
             .I0  (l[bit_cnt]),
             .I1  (hh[bit_cnt]),
             .S   (S[3]),
             .O   (o_i[bit_cnt])
            ); 
          end
        end
          
        13,14,15,16: begin
          assign ll = f_mux4(S[1:0], A[0 +: 4*C_DATA_WIDTH]);
          assign lh = f_mux4(S[1:0], A[4*C_DATA_WIDTH +: 4*C_DATA_WIDTH]);
          assign hl = f_mux4(S[1:0], A[8*C_DATA_WIDTH +: 4*C_DATA_WIDTH]);
          for (bit_cnt = 0; bit_cnt < C_DATA_WIDTH ; bit_cnt = bit_cnt + 1) begin : gen_mux_13_16
            MUXF7 muxf_s2_low_inst 
            (
             .I0  (ll[bit_cnt]),
             .I1  (lh[bit_cnt]),
             .S   (S[2]),
             .O   (l[bit_cnt])
            ); 
            MUXF7 muxf_s2_hi_inst 
            (
             .I0  (hl[bit_cnt]),
             .I1  (hh[bit_cnt]),
             .S   (S[2]),
             .O   (h[bit_cnt])
            );
          
            MUXF8 muxf_s3_inst 
            (
             .I0  (l[bit_cnt]),
             .I1  (h[bit_cnt]),
             .S   (S[3]),
             .O   (o_i[bit_cnt])
            ); 
          end
        end
          
        17: begin
          assign ll = S[4] ? A[16*C_DATA_WIDTH +: C_DATA_WIDTH] : f_mux4(S[1:0], A[0 +: 4*C_DATA_WIDTH]);  assign lh = f_mux4(S[1:0], A[4*C_DATA_WIDTH +: 4*C_DATA_WIDTH]);
          assign hl = f_mux4(S[1:0], A[8*C_DATA_WIDTH +: 4*C_DATA_WIDTH]);
          for (bit_cnt = 0; bit_cnt < C_DATA_WIDTH ; bit_cnt = bit_cnt + 1) begin : gen_mux_17
            MUXF7 muxf_s2_low_inst 
            (
             .I0  (ll[bit_cnt]),
             .I1  (lh[bit_cnt]),
             .S   (S[2]),
             .O   (l[bit_cnt])
            ); 
            MUXF7 muxf_s2_hi_inst 
            (
             .I0  (hl[bit_cnt]),
             .I1  (hh[bit_cnt]),
             .S   (S[2]),
             .O   (h[bit_cnt])
            ); 
            MUXF8 muxf_s3_inst 
            (
             .I0  (l[bit_cnt]),
             .I1  (h[bit_cnt]),
             .S   (S[3]),
             .O   (o_i[bit_cnt])
            ); 
          end
        end
          
        default:  assign o_i = f_mux(S, A);
      endcase
    end  endgenerate
endmodule
