/**************************************************************************/
/* code190_ss.v                          For CSC.T341 CLD Archlab TOKYO TECH */
/**************************************************************************/
`timescale 1ns/100ps
`default_nettype none //

/***** top module for simulation *****/
module m_top (); 
  reg r_clk=0; initial forever #50 r_clk = ~r_clk;
  wire [31:0] w_led;

//  initial $dumpfile("main.vcd");
//  initial $dumpvars(0, m_top);

  reg [31:0] r_cnt = 1;
  always@(posedge r_clk) r_cnt <= r_cnt + 1;
   
  m_proc14 p (r_clk, 1'b1, w_led);

  always@(posedge r_clk) $write("%7d %08x %08x\n", 
                r_cnt, p.Wb_rslt2, p.Wb_rslt2_2);
//  initial begin
//     $write("clock: r_pc     IfId_pc  IdEx_pc  ExMe_pc  MeWb_pc : ");
//     $write("t Id_rrs1  Id_rrs2  Ex_ain   Ex_rslt  Wb_rslt2 w_led\n");
//  end
//  always@(posedge r_clk) 
//    $write("%5d: %08x %08x %08x %08x %08x: %d %08x %08x %08x %08x %08x %08x\n", 
//           r_cnt, p.r_pc, p.IfId_pc, p.IdEx_pc, p.ExMe_pc, p.MeWb_pc,  
//           p.Ex_taken, p.Id_rrs1, p.Id_rrs2, p.Ex_ain, p.Ex_rslt, p.Wb_rslt2, p.w_led);
  always@(posedge r_clk) if(w_led!=0) $finish;
  initial #30000000 $finish;
endmodule

/***** main module for FPGA implementation *****/
/*
module m_main (w_clk, w_led);
  input  wire w_clk;
  output wire [3:0] w_led;
 
  wire w_clk2, w_locked;
  clk_wiz_0 clk_w0 (w_clk2, 0, w_locked, w_clk);
   
  wire [31:0] w_dout;
  m_proc14 p (w_clk2, w_locked, w_dout);

  vio_0 vio_00(w_clk2, w_dout);
 
  reg [3:0] r_led = 0;
  always @(posedge w_clk2) 
    r_led <= {^w_dout[31:24], ^w_dout[23:16], ^w_dout[15:8], ^w_dout[7:0]};
  assign w_led = r_led;
endmodule
*/

/**************************************************************************/
module m_proc14 (w_clk, w_ce, w_led);
  input  wire w_clk, w_ce;
  output wire [31:0] w_led;

  reg [31:0] r_pc_ss    = 0; // program counter
  reg [0:0]  IfId_vb_ss = 0; // 2本目のラインの有効性
  reg [0:0]  IdEx_vb_ss = 0;
  reg [0:0]  ExMe_vb_ss = 0;
  reg [0:0]  MeWb_vb_ss = 0;

  // 1本目のラインのレジスタ
  reg [31:0] IfId_pc   = 0; // IfId pipeline registers
  reg [31:0] IfId_ir   = 0;

  reg [31:0] IdEx_pc   = 0; // IdEx pipeline registers
  reg [31:0] IdEx_ir   = 0;   
  reg [31:0] IdEx_tpc  = 0;
  reg [31:0] IdEx_rrs1 = 0;
  reg [31:0] IdEx_rrs2 = 0;   
  reg [31:0] IdEx_imm  = 0;
  reg [4:0]  IdEx_rd   = 0;

  reg [31:0] ExMe_pc   = 0; // ExMe pipeline registers
  reg [31:0] ExMe_ir   = 0;
  reg [31:0] ExMe_rslt = 0;
  reg [31:0] ExMe_rrs2 = 0;
  reg [4:0]  ExMe_rd   = 0;

  reg [31:0] MeWb_pc   = 0; // MeWb pipeline registers
  reg [31:0] MeWb_ir   = 0;
  reg [31:0] MeWb_rslt = 0;
  reg [31:0] MeWb_ldd  = 0;
  reg [4:0]  MeWb_rd   = 0;

  // 2本目のラインのレジスタ
  reg [31:0] IfId_pc_2   = 0; // IfId pipeline registers
  reg [31:0] IfId_ir_2   = 0;

  reg [31:0] IdEx_pc_2   = 0; // IdEx pipeline registers
  reg [31:0] IdEx_ir_2   = 0;   
  reg [31:0] IdEx_tpc_2  = 0;
  reg [31:0] IdEx_rrs1_2 = 0;
  reg [31:0] IdEx_rrs2_2 = 0;   
  reg [31:0] IdEx_imm_2  = 0;
  reg [4:0]  IdEx_rd_2   = 0;

  reg [31:0] ExMe_pc_2   = 0; // ExMe pipeline registers
  reg [31:0] ExMe_ir_2   = 0;
  reg [31:0] ExMe_rslt_2 = 0;
  reg [31:0] ExMe_rrs2_2 = 0;
  reg [4:0]  ExMe_rd_2   = 0;

  reg [31:0] MeWb_pc_2   = 0; // MeWb pipeline registers
  reg [31:0] MeWb_ir_2   = 0;
  reg [31:0] MeWb_rslt_2 = 0;
  reg [31:0] MeWb_ldd_2  = 0;
  reg [4:0]  MeWb_rd_2   = 0;
  /*********************** IF stage *********************************/
  wire [0:0] w_vb_ss;
  wire [31:0] If_ir, If_ir_2;
  m_inst_dep_ss m_imem_ss (r_pc_ss[13:2], w_vb_ss, If_ir, If_ir_2);
  always @(posedge w_clk) #5 if(w_ce) begin
    IfId_vb_ss <= w_vb_ss;
    // 1本目
    IfId_pc <= (Ex_taken || Ex_taken_2) ? 0 : r_pc_ss;
    IfId_ir <= (Ex_taken || Ex_taken_2) ? {25'd0, 7'b0010011} : If_ir;
    // 2本目
    IfId_pc_2 <= (Ex_taken || Ex_taken_2) ? 0 : r_pc_ss+4;
    IfId_ir_2 <= (Ex_taken || Ex_taken_2) ? {25'd0, 7'b0010011} : If_ir_2;
  end
  /*********************** ID stage *********************************/
  // 1本目
  wire [4:0] Id_op5 = IfId_ir[6:2];
  wire [4:0] Id_rs1 = IfId_ir[19:15];
  wire [4:0] Id_rs2 = IfId_ir[24:20];
  wire [4:0] Id_rd  = IfId_ir[11:7];
  wire Id_we = (Id_op5==5'b01100 || Id_op5==5'b00100 || Id_op5==5'b00000);
  wire [31:0] Id_imm, Id_rrs1, Id_rrs2;
  m_immgen m_immgen0 (IfId_ir, Id_imm);
  // 2本目
  wire [4:0] Id_op5_2 = IfId_ir_2[6:2];
  wire [4:0] Id_rs1_2 = IfId_ir_2[19:15];
  wire [4:0] Id_rs2_2 = IfId_ir_2[24:20];
  wire [4:0] Id_rd_2  = IfId_ir_2[11:7];
  wire Id_we_2 = (Id_op5_2==5'b01100 || Id_op5_2==5'b00100 || Id_op5_2==5'b00000);
  wire [31:0] Id_imm_2, Id_rrs1_2, Id_rrs2_2;
  m_immgen m_immgen0_2 (IfId_ir_2, Id_imm_2);

  m_rf_bypass_ss m_regs (w_clk, Id_rs1, Id_rs1_2, Id_rs2, Id_rs2_2, MeWb_rd, MeWb_rd_2, 1'b1, Wb_rslt2, Wb_rslt2_2, Id_rrs1, Id_rrs1_2, Id_rrs2, Id_rrs2_2);

  always @(posedge w_clk) #5 if(w_ce) begin
    IdEx_vb_ss <= IfId_vb_ss;
    // 1本目
    IdEx_pc   <= (Ex_taken || Ex_taken_2) ? 0 : IfId_pc;
    IdEx_ir   <= (Ex_taken || Ex_taken_2) ? {25'd0, 7'b0010011} : IfId_ir;
    IdEx_tpc  <= IfId_pc + Id_imm;
    IdEx_imm  <= Id_imm;
    IdEx_rrs1 <= Id_rrs1;
    IdEx_rrs2 <= Id_rrs2;
    IdEx_rd   <= (Id_we==0 || Ex_taken || Ex_taken_2) ? 0 : Id_rd; // Note
    // 2本目
    IdEx_pc_2   <= (Ex_taken || Ex_taken_2) ? 0 : IfId_pc_2;
    IdEx_ir_2   <= (Ex_taken || Ex_taken_2) ? {25'd0, 7'b0010011} : IfId_ir_2;
    IdEx_tpc_2  <= IfId_pc_2 + Id_imm_2;
    IdEx_imm_2  <= Id_imm_2;
    IdEx_rrs1_2 <= Id_rrs1_2;
    IdEx_rrs2_2 <= Id_rrs2_2;
    IdEx_rd_2   <= (Id_we_2==0 || Ex_taken || Ex_taken_2) ? 0 : Id_rd_2; // Note
  end
  /*********************** Ex stage *********************************/
  // 1本目
  wire [4:0] Ex_op5 = IdEx_ir[6:2];
  wire [4:0] Ex_rs1 = IdEx_ir[19:15]; // 5/23
  wire [4:0] Ex_rs2 = IdEx_ir[24:20]; // 5/23
  wire Ex_SLL = (IdEx_ir[14:12]==3'b001);
  wire Ex_SRL = (IdEx_ir[14:12]==3'b101);
  wire Ex_BEQ = ({IdEx_ir[12], Ex_op5}==6'b011000);
  wire Ex_BNE = ({IdEx_ir[12], Ex_op5}==6'b111000);
  wire [31:0] Ex_ain1 = (Ex_rs1==0) ? 0 : (Ex_rs1==Me_rd & Me_we) ? ExMe_rslt : (Ex_rs1==Wb_rd & Wb_we) ? Wb_rslt2 : 
                                          (Ex_rs1==Me_rd_2 & Me_we_2) ? ExMe_rslt_2 : (Ex_rs1==Wb_rd_2 & Wb_we_2) ? Wb_rslt2_2 : IdEx_rrs1; // 5/23
  wire [31:0] Ex_ain2 = (Ex_rs2==0) ? 0 : (Ex_rs2==Me_rd & Me_we) ? ExMe_rslt : (Ex_rs2==Wb_rd & Wb_we) ? Wb_rslt2 : 
                                          (Ex_rs2==Me_rd_2 & Me_we_2) ? ExMe_rslt_2 : (Ex_rs2==Wb_rd_2 & Wb_we_2) ? Wb_rslt2_2 : IdEx_rrs2; // 5/23
  wire [31:0] Ex_ain = (Ex_op5==5'b01100 || Ex_op5==5'b11000) ? Ex_ain2 : IdEx_imm; // 5/23
  wire [31:0] Ex_rslt = (Ex_SLL) ? Ex_ain1 << Ex_ain[4:0] : // 5/23
                        (Ex_SRL) ? Ex_ain1 >> Ex_ain[4:0] : Ex_ain1 + Ex_ain; // 5/23
  wire Ex_taken = (Ex_BEQ & Ex_ain1==Ex_ain) || (Ex_BNE & Ex_ain1!=Ex_ain); // 5/23
  // 2本目
  wire [4:0] Ex_op5_2 = IdEx_ir_2[6:2];
  wire [4:0] Ex_rs1_2 = IdEx_ir_2[19:15]; // 5/23
  wire [4:0] Ex_rs2_2 = IdEx_ir_2[24:20]; // 5/23
  wire Ex_SLL_2 = (IdEx_ir_2[14:12]==3'b001);
  wire Ex_SRL_2 = (IdEx_ir_2[14:12]==3'b101);
  wire Ex_BEQ_2 = ({IdEx_ir_2[12], Ex_op5_2}==6'b011000);
  wire Ex_BNE_2 = ({IdEx_ir_2[12], Ex_op5_2}==6'b111000);
  wire [31:0] Ex_ain1_2 = (Ex_rs1_2==0) ? 0 : (Ex_rs1_2==Me_rd & Me_we) ? ExMe_rslt : (Ex_rs1_2==Wb_rd & Wb_we) ? Wb_rslt2 : 
                                              (Ex_rs1_2==Me_rd_2 & Me_we_2) ? ExMe_rslt_2 : (Ex_rs1_2==Wb_rd_2 & Wb_we_2) ? Wb_rslt2_2 : IdEx_rrs1_2; // 5/23
  wire [31:0] Ex_ain2_2 = (Ex_rs2_2==0) ? 0 : (Ex_rs2_2==Me_rd & Me_we) ? ExMe_rslt : (Ex_rs2_2==Wb_rd & Wb_we) ? Wb_rslt2 : 
                                              (Ex_rs2_2==Me_rd_2 & Me_we_2) ? ExMe_rslt_2 : (Ex_rs2_2==Wb_rd_2 & Wb_we_2) ? Wb_rslt2_2 : IdEx_rrs2_2; // 5/23
  wire [31:0] Ex_ain_2 = (Ex_op5_2==5'b01100 || Ex_op5_2==5'b11000) ? Ex_ain2_2 : IdEx_imm_2; // 5/23
  wire [31:0] Ex_rslt_2 = (Ex_SLL_2) ? Ex_ain1_2 << Ex_ain_2[4:0] : // 5/23
                          (Ex_SRL_2) ? Ex_ain1_2 >> Ex_ain_2[4:0] : Ex_ain1_2 + Ex_ain_2; // 5/23
  wire Ex_taken_2 = (Ex_BEQ_2 & Ex_ain1_2==Ex_ain_2) || (Ex_BNE_2 & Ex_ain1_2!=Ex_ain_2); // 5/23

  always @(posedge w_clk) #5 if(w_ce) begin
    ExMe_vb_ss <= IdEx_vb_ss;
    // 1本目
    ExMe_pc   <= IdEx_pc;
    ExMe_ir   <= IdEx_ir;
    ExMe_rslt <= Ex_rslt;
    ExMe_rrs2 <= IdEx_rrs2;
    ExMe_rd   <= IdEx_rd;
    // 2本目
    ExMe_pc_2   <= (Ex_taken) ? 0 : IdEx_pc_2;
    ExMe_ir_2   <= (Ex_taken) ? {25'd0, 7'b0010011} : IdEx_ir_2;
    ExMe_rslt_2 <= Ex_rslt_2;
    ExMe_rrs2_2 <= IdEx_rrs2_2;
    ExMe_rd_2   <= (Ex_taken) ? 0 : IdEx_rd_2;
  end
  /*********************** Me stage *********************************/
  // 1本目
  wire [4:0] Me_op5 = ExMe_ir[6:2];   
  wire [4:0] Me_rd = ExMe_rd; // 5/23
  wire       Me_we = (Me_op5==5'b01100 || Me_op5==5'b00100 || Me_op5==5'b00000);
  wire [31:0] Me_ldd;
  // 2本目
  wire [4:0] Me_op5_2 = ExMe_ir_2[6:2];   
  wire [4:0] Me_rd_2 = ExMe_rd_2; // 5/23
  wire       Me_we_2 = (Me_op5_2==5'b01100 || Me_op5_2==5'b00100 || Me_op5_2==5'b00000);
  wire [31:0] Me_ldd_2;

  m_amemory_ss m_dmem_ss (w_clk, ExMe_rslt[13:2], ExMe_rslt_2[13:2], (Me_op5==5'b01000), (Me_op5_2==5'b01000), ExMe_rrs2, ExMe_rrs2_2, Me_ldd, Me_ldd_2);

  always @(posedge w_clk) #5 if(w_ce) begin
    MeWb_vb_ss <= ExMe_vb_ss;
    // 1本目
    MeWb_pc   <= ExMe_pc;
    MeWb_ir   <= ExMe_ir;
    MeWb_rslt <= ExMe_rslt;
    MeWb_ldd  <= Me_ldd;
    MeWb_rd   <= ExMe_rd;
    // 2本目
    MeWb_pc_2   <= ExMe_pc_2;
    MeWb_ir_2   <= ExMe_ir_2;
    MeWb_rslt_2 <= ExMe_rslt_2;
    MeWb_ldd_2  <= Me_ldd_2;
    MeWb_rd_2   <= ExMe_rd_2;
  end
  /*********************** Wb stage *********************************/
  // 1本目
  wire Wb_LW = (MeWb_ir[6:2]==5'b00000);
  wire [4:0] Wb_op5 = MeWb_ir[6:2]; // 5/23
  wire [4:0] Wb_rd = MeWb_rd; // 5/23
  wire       Wb_we = (Wb_op5==5'b01100 || Wb_op5==5'b00100 || Wb_op5==5'b00000); // 5/23
  wire [31:0] Wb_rslt2 = (Wb_LW) ? MeWb_ldd : MeWb_rslt;
  // 2本目
  wire Wb_LW_2 = (MeWb_ir_2[6:2]==5'b00000);
  wire [4:0] Wb_op5_2 = MeWb_ir_2[6:2]; // 5/23
  wire [4:0] Wb_rd_2 = MeWb_rd_2; // 5/23
  wire       Wb_we_2 = (Wb_op5_2==5'b01100 || Wb_op5_2==5'b00100 || Wb_op5_2==5'b00000); // 5/23
  wire [31:0] Wb_rslt2_2 = (Wb_LW_2) ? MeWb_ldd_2 : MeWb_rslt_2;

  always @(posedge w_clk) #5 begin
    if(w_ce && IfId_ir!=32'h000f0033 && IfId_ir_2!=32'h000f0033) r_pc_ss <= (Ex_taken) ? IdEx_tpc : (Ex_taken_2) ? IdEx_tpc_2 : 
                                                                            (w_vb_ss) ? r_pc_ss+8 : r_pc_ss+4;
  end
   
  reg [31:0] r_led = 0;
  always @(posedge w_clk) begin 
    if(w_ce & MeWb_rd==30) r_led <= Wb_rslt2;
    else if(w_ce & MeWb_rd_2==30) r_led <= Wb_rslt2_2;
  end
  assign w_led = r_led;
endmodule

/**************************************************************************/
module m_immgen (w_i, r_imm); // module immediate generator
  input  wire [31:0] w_i;    // instruction
  output reg  [31:0] r_imm;  // r_immediate

  always @(*) case (w_i[6:2])
    5'b11000: r_imm <= {{20{w_i[31]}}, w_i[7], w_i[30:25], w_i[11:8], 1'b0};   // B-type
    5'b01000: r_imm <= {{21{w_i[31]}}, w_i[30:25], w_i[11:7]};                 // S-type
    5'b11011: r_imm <= {{12{w_i[31]}}, w_i[19:12], w_i[20], w_i[30:21], 1'b0}; // J-type
    5'b01101: r_imm <= {w_i[31:12], 12'b0};                                    // U-type
    5'b00101: r_imm <= {w_i[31:12], 12'b0};                                    // U-type
    default : r_imm <= {{21{w_i[31]}}, w_i[30:20]};                   // I-type & R-type
  endcase
endmodule

/**************************************************************************/
module m_inst_dep_ss (w_addr, r_vb, w_dout, w_dout_2); // 命令列をフェッチし依存性を確認
  input  wire [11:0] w_addr;
  output reg [0:0] r_vb;
  output wire [31:0] w_dout, w_dout_2;
  reg [31:0] 	     cm_ram [0:4095]; // 4K word (4096 x 32bit) memory
  
  // 依存性の確認
  wire [4:0] w_op = cm_ram[w_addr][6:2];
  wire [4:0] w_rs1 = cm_ram[w_addr][19:15];
  wire [4:0] w_rs2 = cm_ram[w_addr][24:20];
  wire [4:0] w_rd = cm_ram[w_addr][11:7];
  wire [4:0] w_op_2 = cm_ram[w_addr+1][6:2];
  wire [4:0] w_rs1_2 = cm_ram[w_addr+1][19:15];
  wire [4:0] w_rs2_2 = cm_ram[w_addr+1][24:20];
  wire [4:0] w_rd_2 = cm_ram[w_addr+1][11:7];

  always @(*) #5 case (w_op[4:3])
    2'b00: case (w_op_2[4:3])
      // 1本目がI-typeのとき
      2'b00: r_vb <= (w_rd!=w_rs1_2 & w_rd!=w_rd_2 & w_rs1!=w_rd_2);
      2'b01: r_vb <= (w_rd!=w_rs1_2 & w_rd!=w_rs2_2 & w_rd!=w_rd_2 & w_rs1!=w_rd_2);
      default: r_vb <= (w_rd!=w_rs1_2 & w_rd!=w_rs2_2);
    endcase
    2'b01: case (w_op_2[4:3])
      // 1本目がR-typeのとき
      2'b00: r_vb <= (w_rd!=w_rs1_2 & w_rd!=w_rd_2 & w_rs1!=w_rd_2 & w_rs2!=w_rd_2);
      2'b01: r_vb <= (w_rd!=w_rs1_2 & w_rd!=w_rs2_2 & w_rd!=w_rd_2 & w_rs1!=w_rd_2 & w_rs2!=w_rd_2);
      default: r_vb <= (w_rd!=w_rs1_2 & w_rd!=w_rs2_2);
    endcase
    2'b01: case (w_op_2[4:2])
      // 1本目がS-typeのとき
      3'b010: r_vb <= 1'b0; // sw
      3'b000: r_vb <= 1'b0; // lw
      default: r_vb <= 1'b1;
    endcase
    default: r_vb <= 1'b1; // 1本目がB-typeのとき
  endcase

  // 命令列のフェッチ
  assign #15 w_dout = cm_ram[w_addr];
  assign #15 w_dout_2 = (r_vb) ? cm_ram[w_addr+1] : {25'd0, 7'b0010011};

`include "program.txt"
endmodule

/**************************************************************************/
module m_rf_bypass_ss (w_clk, w_rr1, w_rr1_2, w_rr2, w_rr2_2, w_wr, w_wr_2, w_we, w_wdata, w_wdata_2, w_rdata1, w_rdata1_2, w_rdata2, w_rdata2_2); // 5/23
  input  wire        w_clk;
  input  wire [4:0]  w_rr1, w_rr2, w_wr, w_rr1_2, w_rr2_2, w_wr_2;
  input  wire [31:0] w_wdata, w_wdata_2;
  input  wire        w_we;
  output wire [31:0] w_rdata1, w_rdata2,  w_rdata1_2, w_rdata2_2;
    
  reg [31:0] r[0:31];
  assign #8 w_rdata1 = (w_rr1==0) ? 0 : (w_rr1==w_wr & w_we) ? w_wdata : (w_rr1==w_wr_2 & w_we) ? w_wdata_2 : r[w_rr1]; // 5/23
  assign #8 w_rdata2 = (w_rr2==0) ? 0 : (w_rr2==w_wr & w_we) ? w_wdata : (w_rr2==w_wr_2 & w_we) ? w_wdata_2 : r[w_rr2]; // 5/23
  assign #8 w_rdata1_2 = (w_rr1_2==0) ? 0 : (w_rr1_2==w_wr & w_we) ? w_wdata : (w_rr1_2==w_wr_2 & w_we) ? w_wdata_2 : r[w_rr1_2]; 
  assign #8 w_rdata2_2 = (w_rr2_2==0) ? 0 : (w_rr2_2==w_wr & w_we) ? w_wdata : (w_rr2_2==w_wr_2 & w_we) ? w_wdata_2 : r[w_rr2_2]; 
  always @(posedge w_clk) if(w_we) begin
    r[w_wr] <= w_wdata;
    r[w_wr_2] <= w_wdata_2;
  end
endmodule

/**************************************************************************/
module m_amemory_ss (w_clk, w_addr, w_addr_2, w_we, w_we_2, w_din, w_din_2, w_dout, w_dout_2); // asynchronous memory
  input  wire w_clk, w_we, w_we_2;
  input  wire [11:0] w_addr, w_addr_2;
  input  wire [31:0] w_din, w_din_2;
  output wire [31:0] w_dout, w_dout_2;
  reg [31:0] 	     cm_ram [0:4095]; // 4K word (4096 x 32bit) memory
  always @(posedge w_clk) begin 
    if (w_we) cm_ram[w_addr] <= w_din;
    else if (w_we_2) cm_ram[w_addr_2] <= w_din_2;
  end
  assign #20 w_dout = cm_ram[w_addr];
  assign #20 w_dout_2 = cm_ram[w_addr_2];
endmodule
/**************************************************************************/