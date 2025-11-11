// SVA for EHRU_8: priority-write chain correctness, next-cycle update, X checks, and targeted coverage.
// Bindable assertion module (concise, param-aware, no TB code).
module EHRU_8_sva #(parameter DATA_SZ = 1)
(
  input  logic                CLK,
  // inputs
  input  logic [DATA_SZ-1:0] write_0, write_1, write_2, write_3, write_4, write_5, write_6, write_7,
  input  logic               EN_write_0, EN_write_1, EN_write_2, EN_write_3, EN_write_4, EN_write_5, EN_write_6, EN_write_7,
  // outputs
  input  logic [DATA_SZ-1:0] read_0, read_1, read_2, read_3, read_4, read_5, read_6, read_7,
  // internal
  input  logic [DATA_SZ-1:0] r
);

  default clocking cb @(posedge CLK); endclocking

  // Pack into arrays for compact properties
  logic               en [0:7];
  logic [DATA_SZ-1:0] w  [0:7];
  logic [DATA_SZ-1:0] rd [0:7];

  assign en[0]=EN_write_0; assign en[1]=EN_write_1; assign en[2]=EN_write_2; assign en[3]=EN_write_3;
  assign en[4]=EN_write_4; assign en[5]=EN_write_5; assign en[6]=EN_write_6; assign en[7]=EN_write_7;
  assign w[0]=write_0;     assign w[1]=write_1;     assign w[2]=write_2;     assign w[3]=write_3;
  assign w[4]=write_4;     assign w[5]=write_5;     assign w[6]=write_6;     assign w[7]=write_7;
  assign rd[0]=read_0;     assign rd[1]=read_1;     assign rd[2]=read_2;     assign rd[3]=read_3;
  assign rd[4]=read_4;     assign rd[5]=read_5;     assign rd[6]=read_6;     assign rd[7]=read_7;

  // Combinational chain correctness (read_0 mirrors r; each stage is a 1-deep priority mux)
  assert property (read_0 == r);
  genvar k;
  generate
    for (k=0; k<7; k++) begin : g_chain
      assert property (rd[k+1] == (en[k] ? w[k] : rd[k]));
    end
  endgenerate

  // Registered update: r on next cycle equals final stage (EN7 ? write7 : read7) of prior cycle
  assert property (1'b1 |-> ##1 (r == $past(en[7] ? w[7] : rd[7])));

  // Hold when no writes
  assert property ((!(en[0]|en[1]|en[2]|en[3]|en[4]|en[5]|en[6]|en[7])) |=> (r == $past(r)));

  // Priority winner for each write index j (no higher enable overrides)
  genvar j;
  generate
    for (j=0; j<8; j++) begin : g_prio
      // No higher enables than j
      wire no_higher = (j==7) ? 1'b1 :
                       ~(|{en[7], en[6], en[5], en[4], en[3], en[2], en[1]} >> (7-(j+1)));
      // Assertion: highest-enabled index drives next r
      assert property (en[j] && no_higher |=> (r == $past(w[j])));
    end
  endgenerate

  // Sanity/X checks
  assert property (!$isunknown({EN_write_0,EN_write_1,EN_write_2,EN_write_3,EN_write_4,EN_write_5,EN_write_6,EN_write_7}));      // enables known
  assert property (!$isunknown({r, read_0,read_1,read_2,read_3,read_4,read_5,read_6,read_7}));                                   // outputs/state known
  generate
    for (k=0; k<8; k++) begin : g_w_known_when_en
      assert property (en[k] |-> !$isunknown(w[k]));                                                                              // data known when used
    end
  endgenerate

  // Coverage: each priority slot wins once; no-write hold case
  generate
    for (j=0; j<8; j++) begin : g_cov_win
      wire no_higher = (j==7) ? 1'b1 :
                       ~(|{en[7], en[6], en[5], en[4], en[3], en[2], en[1]} >> (7-(j+1)));
      cover property (en[j] && no_higher ##1 (r == $past(w[j])));
    end
  endgenerate
  cover property ((!(en[0]|en[1]|en[2]|en[3]|en[4]|en[5]|en[6]|en[7])) ##1 (r == $past(r)));

endmodule

// Bind into DUT (connects to internal r)
bind EHRU_8 EHRU_8_sva #(.DATA_SZ(DATA_SZ)) EHRU_8_sva_i
(
  .CLK(CLK),
  .write_0(write_0), .write_1(write_1), .write_2(write_2), .write_3(write_3),
  .write_4(write_4), .write_5(write_5), .write_6(write_6), .write_7(write_7),
  .EN_write_0(EN_write_0), .EN_write_1(EN_write_1), .EN_write_2(EN_write_2), .EN_write_3(EN_write_3),
  .EN_write_4(EN_write_4), .EN_write_5(EN_write_5), .EN_write_6(EN_write_6), .EN_write_7(EN_write_7),
  .read_0(read_0), .read_1(read_1), .read_2(read_2), .read_3(read_3),
  .read_4(read_4), .read_5(read_5), .read_6(read_6), .read_7(read_7),
  .r(r)
);