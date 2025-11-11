// SVA for SYM_GEN_4BYTE
// Non-intrusive: uses only DUT ports, models internal pipeline via $past()
// Bind into your design with the bind line at bottom.

module SYM_GEN_4BYTE_sva
(
  input  [0:1]  GEN_SCP,
  input  [0:1]  GEN_ECP,
  input  [0:1]  GEN_PAD,
  input  [0:31] TX_PE_DATA,
  input  [0:1]  TX_PE_DATA_V,
  input         GEN_CC,

  input         GEN_A,
  input  [0:3]  GEN_K,
  input  [0:3]  GEN_R,
  input  [0:3]  GEN_V,
  input         GEN_SP,
  input         GEN_SPA,

  input  [3:0]  TX_CHAR_IS_K,
  input  [31:0] TX_DATA,

  input         USER_CLK
);

  // clocking and init to make $past() well-defined
  bit init_done;
  initial init_done = 0;
  always @(posedge USER_CLK) init_done <= 1'b1;

  default clocking cb @ (posedge USER_CLK); endclocking

  // Helpers: past-cycle “idle” enables (match DUT idle_c[x])
  let idle0_p = !($past(GEN_SCP[0]) || $past(GEN_ECP[0]) || $past(TX_PE_DATA_V[0]) || $past(GEN_CC) || $past(GEN_SP) || $past(GEN_SPA) || $past(GEN_V[0]));
  let idle1_p = !($past(GEN_SCP[0]) || $past(GEN_ECP[0]) || $past(TX_PE_DATA_V[0]) || $past(GEN_CC) || $past(GEN_SP) || $past(GEN_SPA) || $past(GEN_V[1]));
  let idle2_p = !($past(GEN_SCP[1]) || $past(GEN_ECP[1]) || $past(TX_PE_DATA_V[1]) || $past(GEN_CC) || $past(GEN_SP) || $past(GEN_SPA) || $past(GEN_V[2]));
  let idle3_p = !($past(GEN_SCP[1]) || $past(GEN_ECP[1]) || $past(TX_PE_DATA_V[1]) || $past(GEN_CC) || $past(GEN_SP) || $past(GEN_SPA) || $past(GEN_V[3]));

  // Highest-priority: V characters on each lane
  assert property (disable iff (!init_done) $past(GEN_V[0]) |-> TX_DATA[31:24] == 8'hE8);
  assert property (disable iff (!init_done) $past(GEN_V[1]) |-> TX_DATA[23:16] == 8'hE8);
  assert property (disable iff (!init_done) $past(GEN_V[2]) |-> TX_DATA[15:8]  == 8'hE8);
  assert property (disable iff (!init_done) $past(GEN_V[3]) |-> TX_DATA[7:0]   == 8'hE8);

  // SPA and SP multi-byte primitives (block if any V present)
  assert property (disable iff (!init_done)
    $past(GEN_SPA) && !($past(GEN_V[0])||$past(GEN_V[1])||$past(GEN_V[2])||$past(GEN_V[3]))
    |-> TX_DATA == 32'hBC2C2C2C);

  assert property (disable iff (!init_done)
    $past(GEN_SP) && !$past(GEN_SPA) &&
    !($past(GEN_V[0])||$past(GEN_V[1])||$past(GEN_V[2])||$past(GEN_V[3]))
    |-> TX_DATA == 32'hBC4A4A4A);

  // CC primitive (wins over data/SCP/ECP, blocked by SP/SPA/V)
  assert property (disable iff (!init_done)
    $past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) &&
    !($past(GEN_V[0])||$past(GEN_V[1])||$past(GEN_V[2])||$past(GEN_V[3]))
    |-> TX_DATA == {4{8'hF7}});

  // SCP/ECP (per half; blocked by ECP->SCP, data_v, CC, SP/SPA, V on that lane)
  // Upper half (index 0): lanes [31:24]=5C/FD, [23:16]=FB/FE
  assert property (disable iff (!init_done)
    $past(GEN_SCP[0]) && !$past(GEN_ECP[0]) && !$past(TX_PE_DATA_V[0]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[0])
    |-> TX_DATA[31:24] == 8'h5C);
  assert property (disable iff (!init_done)
    $past(GEN_ECP[0]) && !$past(TX_PE_DATA_V[0]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[0])
    |-> TX_DATA[31:24] == 8'hFD);

  assert property (disable iff (!init_done)
    $past(GEN_SCP[0]) && !$past(GEN_ECP[0]) && !$past(TX_PE_DATA_V[0]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[1])
    |-> TX_DATA[23:16] == 8'hFB);
  assert property (disable iff (!init_done)
    $past(GEN_ECP[0]) && !$past(TX_PE_DATA_V[0]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[1])
    |-> TX_DATA[23:16] == 8'hFE);

  // Lower half (index 1): lanes [15:8]=5C/FD, [7:0]=FB/FE
  assert property (disable iff (!init_done)
    $past(GEN_SCP[1]) && !$past(GEN_ECP[1]) && !$past(TX_PE_DATA_V[1]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[2])
    |-> TX_DATA[15:8] == 8'h5C);
  assert property (disable iff (!init_done)
    $past(GEN_ECP[1]) && !$past(TX_PE_DATA_V[1]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[2])
    |-> TX_DATA[15:8] == 8'hFD);

  assert property (disable iff (!init_done)
    $past(GEN_SCP[1]) && !$past(GEN_ECP[1]) && !$past(TX_PE_DATA_V[1]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[3])
    |-> TX_DATA[7:0] == 8'hFB);
  assert property (disable iff (!init_done)
    $past(GEN_ECP[1]) && !$past(TX_PE_DATA_V[1]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[3])
    |-> TX_DATA[7:0] == 8'hFE);

  // Data path (wins only when no later override: CC/SP/SPA/V)
  // Upper pair
  assert property (disable iff (!init_done)
    $past(TX_PE_DATA_V[0]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[0])
    |-> TX_DATA[31:24] == $past(TX_PE_DATA[0:7]));
  assert property (disable iff (!init_done)
    $past(TX_PE_DATA_V[0] && GEN_PAD[0]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[1])
    |-> TX_DATA[23:16] == 8'h9C);
  assert property (disable iff (!init_done)
    $past(TX_PE_DATA_V[0] && !GEN_PAD[0]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[1])
    |-> TX_DATA[23:16] == $past(TX_PE_DATA[8:15]));

  // Lower pair
  assert property (disable iff (!init_done)
    $past(TX_PE_DATA_V[1]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[2])
    |-> TX_DATA[15:8] == $past(TX_PE_DATA[16:23]));
  assert property (disable iff (!init_done)
    $past(TX_PE_DATA_V[1] && GEN_PAD[1]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[3])
    |-> TX_DATA[7:0] == 8'h9C);
  assert property (disable iff (!init_done)
    $past(TX_PE_DATA_V[1] && !GEN_PAD[1]) && !$past(GEN_CC) && !$past(GEN_SP) && !$past(GEN_SPA) && !$past(GEN_V[3])
    |-> TX_DATA[7:0] == $past(TX_PE_DATA[24:31]));

  // Idle-inserted A/K/R with correct priority (within same idle group)
  // Lane [31:24] (group 0): A < K < R (R overrides K, K overrides A)
  assert property (disable iff (!init_done)
    idle0_p && $past(GEN_A) && !$past(GEN_K[0]) && !$past(GEN_R[0]) |-> TX_DATA[31:24] == 8'h7C);
  assert property (disable iff (!init_done)
    idle0_p && $past(GEN_K[0]) && !$past(GEN_R[0]) |-> TX_DATA[31:24] == 8'hBC);
  assert property (disable iff (!init_done)
    idle0_p && $past(GEN_R[0]) |-> TX_DATA[31:24] == 8'h1C);

  // Lane [23:16] (group 1): K < R
  assert property (disable iff (!init_done)
    idle1_p && $past(GEN_K[1]) && !$past(GEN_R[1]) |-> TX_DATA[23:16] == 8'hBC);
  assert property (disable iff (!init_done)
    idle1_p && $past(GEN_R[1]) |-> TX_DATA[23:16] == 8'h1C);

  // Lane [15:8] (group 2): K < R
  assert property (disable iff (!init_done)
    idle2_p && $past(GEN_K[2]) && !$past(GEN_R[2]) |-> TX_DATA[15:8] == 8'hBC);
  assert property (disable iff (!init_done)
    idle2_p && $past(GEN_R[2]) |-> TX_DATA[15:8] == 8'h1C);

  // Lane [7:0] (group 3): K < R
  assert property (disable iff (!init_done)
    idle3_p && $past(GEN_K[3]) && !$past(GEN_R[3]) |-> TX_DATA[7:0] == 8'hBC);
  assert property (disable iff (!init_done)
    idle3_p && $past(GEN_R[3]) |-> TX_DATA[7:0] == 8'h1C);

  // TX_CHAR_IS_K bits exact formulas
  assert property (disable iff (!init_done)
    TX_CHAR_IS_K[3] == !($past(TX_PE_DATA_V[0]) || $past(GEN_V[0])));
  assert property (disable iff (!init_done)
    TX_CHAR_IS_K[2] == !(($past(TX_PE_DATA_V[0]) && !$past(GEN_PAD[0])) || $past(GEN_SP) || $past(GEN_SPA) || $past(GEN_V[1])));
  assert property (disable iff (!init_done)
    TX_CHAR_IS_K[1] == !($past(TX_PE_DATA_V[1]) || $past(GEN_SP) || $past(GEN_SPA) || $past(GEN_V[2])));
  assert property (disable iff (!init_done)
    TX_CHAR_IS_K[0] == !(($past(TX_PE_DATA_V[1]) && !$past(GEN_PAD[1])) || $past(GEN_SP) || $past(GEN_SPA) || $past(GEN_V[3])));

  // Minimal functional coverage
  cover property (disable iff (!init_done) $past(GEN_SP)  && !($past(GEN_SPA)||$past(GEN_V[0])||$past(GEN_V[1])||$past(GEN_V[2])||$past(GEN_V[3])) ##1 TX_DATA == 32'hBC4A4A4A);
  cover property (disable iff (!init_done) $past(GEN_SPA) && !($past(GEN_V[0])||$past(GEN_V[1])||$past(GEN_V[2])||$past(GEN_V[3])) ##1 TX_DATA == 32'hBC2C2C2C);
  cover property (disable iff (!init_done) $past(GEN_CC)  && !($past(GEN_SP)||$past(GEN_SPA)||$past(GEN_V[0])||$past(GEN_V[1])||$past(GEN_V[2])||$past(GEN_V[3])) ##1 TX_DATA == {4{8'hF7}});
  cover property (disable iff (!init_done) $past(GEN_SCP[0]) && !$past(GEN_ECP[0]||TX_PE_DATA_V[0]||GEN_CC||GEN_SP||GEN_SPA||GEN_V[0]||GEN_V[1]) ##1 (TX_DATA[31:24]==8'h5C && TX_DATA[23:16]==8'hFB));
  cover property (disable iff (!init_done) $past(GEN_ECP[1]) && !$past(TX_PE_DATA_V[1]||GEN_CC||GEN_SP||GEN_SPA||GEN_V[2]||GEN_V[3]) ##1 (TX_DATA[15:8]==8'hFD && TX_DATA[7:0]==8'hFE));
  cover property (disable iff (!init_done) $past(TX_PE_DATA_V[0] && !GEN_PAD[0]) && !$past(GEN_CC||GEN_SP||GEN_SPA||GEN_V[0]||GEN_V[1]) ##1 (TX_DATA[31:24]==$past(TX_PE_DATA[0:7]) && TX_DATA[23:16]==$past(TX_PE_DATA[8:15])));
  cover property (disable iff (!init_done) $past(TX_PE_DATA_V[1] && GEN_PAD[1]) && !$past(GEN_CC||GEN_SP||GEN_SPA||GEN_V[2]||GEN_V[3]) ##1 (TX_DATA[15:8]==$past(TX_PE_DATA[16:23]) && TX_DATA[7:0]==8'h9C));
  cover property (disable iff (!init_done) idle0_p && $past(GEN_A) && !$past(GEN_K[0]||GEN_R[0]) ##1 TX_DATA[31:24]==8'h7C);
  cover property (disable iff (!init_done) idle2_p && $past(GEN_R[2]) ##1 TX_DATA[15:8]==8'h1C);
  cover property (disable iff (!init_done) $past(GEN_V[0]) ##1 TX_DATA[31:24]==8'hE8);
  cover property (disable iff (!init_done) $past(GEN_V[1]) ##1 TX_DATA[23:16]==8'hE8);
  cover property (disable iff (!init_done) $past(GEN_V[2]) ##1 TX_DATA[15:8]==8'hE8);
  cover property (disable iff (!init_done) $past(GEN_V[3]) ##1 TX_DATA[7:0]==8'hE8);

endmodule

// Bind into DUT
bind SYM_GEN_4BYTE SYM_GEN_4BYTE_sva
(
  .GEN_SCP(GEN_SCP),
  .GEN_ECP(GEN_ECP),
  .GEN_PAD(GEN_PAD),
  .TX_PE_DATA(TX_PE_DATA),
  .TX_PE_DATA_V(TX_PE_DATA_V),
  .GEN_CC(GEN_CC),

  .GEN_A(GEN_A),
  .GEN_K(GEN_K),
  .GEN_R(GEN_R),
  .GEN_V(GEN_V),
  .GEN_SP(GEN_SP),
  .GEN_SPA(GEN_SPA),

  .TX_CHAR_IS_K(TX_CHAR_IS_K),
  .TX_DATA(TX_DATA),

  .USER_CLK(USER_CLK)
);