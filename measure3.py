import asyncio
import asyncio.subprocess
import subprocess
import os
import random
import sys
import time
import traceback
from functools import partial
from typing import Union

PROBLEMS = (
    "../data/sat2023/0297c2a35f116ffd5382aea5b421e6df-Urquhart-s3-b3.shuffled-as.sat03-1556.cnf.xz",
    "../data/sat2023/004b0f451f7d96f6a572e9e76360f51a-spg_420_280.cnf.xz",
    "../data/sat2023/008e7716c69009090ff6bd0048dc55f8-SAT_dat.k10.cnf.xz",
    "../data/sat2023/00a981f385cd209d41e1efa1f5f29bac-ibm-2004-03-k70.cnf.xz",
    "../data/sat2023/00b46ace235e3915a439c77a231a5657-TableSymModel_output_7_3_9.bul_.dimacs.cnf.xz",
    "../data/sat2023/00bb0b4ef28ed38c49de4c54b9fabc4d-25_2.cnf.xz",
    "../data/sat2023/00f2eb377986e7decbc863931680a3b2-rand_net70-40-10.shuffled.cnf.xz",
    "../data/sat2023/00f4aca773e5675f35263dcd46b15bde-vmpc_28.shuffled-as.sat05-1957.cnf.xz",
    "../data/sat2023/017ba03ed108f492c9293c7c95e5cae9-multiplier_14bits__miter_14.cnf.xz",
    "../data/sat2023/0191a0bf3412ed407ba669f8d69081ee-mrpp_6x6#18_20.cnf.xz",
    "../data/sat2023/01966a0fc52b2200a13f5f835275a919-SGI_30_70_27_50_3-dir.shuffled-as.sat03-169.cnf.xz",
    "../data/sat2023/01bd0865ab694bc71d80b7d285d5777d-shuffling-2-s1480152728-of-bench-sat04-434.used-as.sat04-711.cnf.xz",
    "../data/sat2023/01dd5feb463fa80f73809718f6ff735b-10pipe_q0_k.cnf.xz",
    "../data/sat2023/02066c116dbacc40ec5cca2067db26c0-mrpp_4x4#12_12.cnf.xz",
    "../data/sat2023/028d0cc7af63e9bba5795f20e24db4f6-pyhala-braun-sat-35-4-04.shuffled.cnf.xz",
    "../data/sat2023/02c6fe8483e4f4474b7ac9731772535d-ncc_none_7047_6_3_3_0_0_420.cnf.xz",
    "../data/sat2023/0336f81b60baac5b8f481dd3c32861a5-mod4block_2vars_10gates_u2_autoenc-sc2009.cnf.xz",
    "../data/sat2023/036b541db9d0839b0591d408ff4f77ae-aes_decry_2_rounds.debugged.cnf.xz",
    "../data/sat2023/037c423f56548082b1935e88c48ffdda-3col120_5_2.shuffled.cnf.xz",
    "../data/sat2023/037d21e060a2e3eab8b080aa84ceee75-mm-1x10-10-10-sb.1.shuffled-as.sat03-1489.cnf.xz",
    "../data/sat2023/03a43a7ea55217f53542ed3f029963af-satch2ways16w.cnf.xz",
    "../data/sat2023/03de316ba1e90305471a3b8620cb9cd7-satsgi-n23himBHm26-p0-q248.cnf.xz",
    "../data/sat2023/03e9d1abe418a1727bbf2ead77d69d02-php15-mixed-15percent-blocked.cnf.xz",
    "../data/sat2023/06b138e8a6da806e88ac7da2919cef30-grs-192-32.cnf.xz",
    "../data/sat2023/075ca0a158690a55b7254d9aaee2e103-asconhashv12_opt64_H4_M2-LOD9_m0_2_U19.c.cnf.xz",
    "../data/sat2023/0811f761eee5e4ef28196fd98884a67b-multiplier_13bits__miter_15.cnf.xz",
    "../data/sat2023/08455b2e1e6fda910989f0481a20f1c3-hash_table_find_safety_size_13.cnf.xz",
    "../data/sat2023/090eefb9bc472f6478e70baf2c6d2403-PRP_100_150.cnf.xz",
    "../data/sat2023/0945c95ba9b82c32d12fc9d9e5229c5a-SC23_Timetable_C_473_E_45_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/096ac97e4261eabca440fc7bc135d7c0-SC23_Timetable_C_478_E_50_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/0982db5b0b15642e79e8242881529b39-REGRandom-K4-L3-Seed15.cnf.xz",
    "../data/sat2023/0a279c478775cdeede51ad431aebf200-24_0.cnf.xz",
    "../data/sat2023/0a4ed112f2cdc0a524976a15d1821097-cliquecoloring_n12_k9_c8.cnf.xz",
    "../data/sat2023/0ae0c5a4fb9001d63669a0aa5b592167-multiplier_16bits__miter_19.cnf.xz",
    "../data/sat2023/0be1e12a8e7282d1a4e389bb90f6dbc7-or_randxor_k3_n600_m600.cnf.xz",
    "../data/sat2023/0c9da400944b002f90fd385d4fdab385-DivS_568_11.cnf.sanitized.cnf.xz",
    "../data/sat2023/0d3e99a07b6a6b67ac59d706c0af9d68-grs-32-160.cnf.xz",
    "../data/sat2023/0eb98926b26343d31954169dfbde2b24-satcoin-genesis-UNSAT-11900.cnf.xz",
    "../data/sat2023/0ef0d91d378eab41ba6fb9dfc9b87fc8-sat-bench-trig-taylor4.cnf.xz",
    "../data/sat2023/10196804504080e7107809a2e5b3bfcc-ContextModel_output_6_5_6.bul_.dimacs.cnf.xz",
    "../data/sat2023/112b0ac22b2a567cd3badfed3a5497fd-mchess16-mixed-35percent-blocked.cnf.xz",
    "../data/sat2023/1153a473e1d5dd21ccd33189d594a4aa-tseitin_d3_n10000.cnf.xz",
    "../data/sat2023/11db226d109e82f93aaa3b2604173ff9-posixpath__joinrealpath_13.cnf.xz",
    "../data/sat2023/14a5ff0d6213dcfe182ec656764bbdfb-satcoin-genesis-UNSAT-9080.cnf.xz",
    "../data/sat2023/150b5f8cac40bb4e0fcbdd65c3c04701-PRP_100_550.cnf.xz",
    "../data/sat2023/15a2ec07aaca45d454a2fbfc0624e75e-hash_table_find_safety_size_29.cnf.xz",
    "../data/sat2023/15c53f73c62a78c24bf5974e4a7afcd8-18_1.cnf.xz",
    "../data/sat2023/17039a3ed02ea12653ec5389e56dab50-pbl-00070.shuffled-as.sat05-1324.shuffled-as.sat05-1324.cnf.xz",
    "../data/sat2023/177a4ad8fd76ad8240387998112c3168-SC23_Timetable_C_481_E_49_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/18416a9ac0909dce5fa96345f784c87e-intervals122.cnf.xz",
    "../data/sat2023/189e5991b041a89700513106988e720d-rphp_p20_r20.cnf.xz",
    "../data/sat2023/18babbd2835b8a37c6299f8b0301c7c9-brent_67_0.05.cnf.xz",
    "../data/sat2023/19004c7d629f7e6e83c6e1d7a9a768a9-6s166.cnf.xz",
    "../data/sat2023/1932e1e8f0c78372759909e45a19ecc7-brent_69_0.3.cnf.xz",
    "../data/sat2023/19c6a29181bee2f3aa03bfb5c5d693d0-brent_9_0.cnf.xz",
    "../data/sat2023/1a20649a8c79d6675d934cec271d573f-tseitin_grid_n100_m100.cnf.xz",
    "../data/sat2023/1a40d2d8c589799a0d267cae03fcd4c5-SCPC-800-40.cnf.xz",
    "../data/sat2023/1a63072b90f88c7fa621b5041f412b79-asconhashv12_opt64_H8_M2-nm2vUdkK_m3_5_U3.c.cnf.xz",
    "../data/sat2023/1a6a635f5b959e191ec705b2f236568a-square.2.0.i.smt2-cvc4.cnf.xz",
    "../data/sat2023/1aa7cd96ab1f7bf58984deccf8362ab4-rand_net50-60-10.shuffled.cnf.xz",
    "../data/sat2023/1b02025658c2a23e1fd3ce0a9c3633cb-asconhashv12_opt64_H8_M2-I61h2mH5_m2_6.c.cnf.xz",
    "../data/sat2023/1b86f59ce4c43f19f0ad1238f8c362b4-PRP_30_37.cnf.xz",
    "../data/sat2023/1ce81dbba1292bf791e194b17aa2a219-satch2ways15u.cnf.xz",
    "../data/sat2023/1d1af993697599892804df5878d58979-brent_69_0.cnf.xz",
    "../data/sat2023/1d42a7c3616ce163e292340cfcd34f97-PRP_100_600.cnf.xz",
    "../data/sat2023/1ea7fe95e6158afe11f7b795b9aac939-REGRandom-K4-L4-Seed10.cnf.xz",
    "../data/sat2023/1eea3d913d346b900252d77fc0cb25c8-par32-4.shuffled.cnf.xz",
    "../data/sat2023/1f215812371f0c428eb1f1e51f9f23d7-20_2.cnf.xz",
    "../data/sat2023/1f6cf91464c6a19022144774b162a3cc-ER_500_30_3.apx_2_DC-ST.cnf.xz",
    "../data/sat2023/20be6aa61af15fd53b4c48eb3f2f3319-27_1.cnf.xz",
    "../data/sat2023/20cae5fe475d571da703f89d5da4bb8f-grs-96-32.cnf.xz",
    "../data/sat2023/211938776d92f11870a687abd11d55a4-iso-icl004.shuffled-as.sat05-3238.cnf.xz",
    "../data/sat2023/21667cf04beae213adbab0d48408a7e4-satcoin-genesis-UNSAT-10600.cnf.xz",
    "../data/sat2023/21bde0ebb111c637a1ae8789827b0b73-WCNF_from_fp_13.cnf.xz",
    "../data/sat2023/220bb8aa093e502c47afcdac3140d67c-vmpc_24.cnf.xz",
    "../data/sat2023/22d0a2fdc65d884c2bbde56af9feba4a-intervals961.cnf.xz",
    "../data/sat2023/23c4e178c94c0dff82ea6c87abed7ecc-rphp_p60_r60.cnf.xz",
    "../data/sat2023/246afd75cb97a21144f368c00252a656-BZ2File_write_11.cnf.xz",
    "../data/sat2023/24b93d0bf941e4b050c9109e4cb7faf4-connm-ue-csp-sat-n600-d-0.02-s1022905465.used-as.sat04-951.cnf.xz",
    "../data/sat2023/24bf910d2b9da558fb3e71a4dbe79ba3-lisa19_99_a.shuffled.cnf.xz",
    "../data/sat2023/2537f10a45d7ab430334dc1de6bfbdf0-SC23_Timetable_C_486_E_50_Cl_33_D_6_T_50.cnf.xz",
    "../data/sat2023/25b7a69d04a5029cf4ba2f483b5bec45-asconhashv12_opt64_H9_M2-LSGb5PgEM_m2_7.c.cnf.xz",
    "../data/sat2023/26114429758a203d651f4df87c94de4c-sgen1-unsat-97-100.cnf.mis-72.debugged.cnf.xz",
    "../data/sat2023/262009b8df6350761c7dfc8761f0af79-intervals788.cnf.xz",
    "../data/sat2023/2722f39c27dc45a989bb52761ed52e50-31_1.cnf.xz",
    "../data/sat2023/275d36e3f246990dccd094e5e1442ba9-WS_500_32_50_10.apx_2_DC-AD.cnf.xz",
    "../data/sat2023/27b4fe4cb0b4e2fd8327209ca5ff352c-grid_10_20.shuffled.cnf.xz",
    "../data/sat2023/28857e681fc6a9077d5a7d0e9c7a19ad-hash_table_find_safety_size_14.cnf.xz",
    "../data/sat2023/28e45a3e488ddac73b6116cc6f3e67e0-g2-T99.2.0.cnf.xz",
    "../data/sat2023/28f29fe949422ec88892e18073de065c-5col100_15_6.shuffled.cnf.xz",
    "../data/sat2023/2902c241b2196f5fd914509fdc124ba7-REGRandom-K4-L2-Seed20.cnf.xz",
    "../data/sat2023/291c2b4fa2d8b009cd2a8331891ba667-PRP_30_40.cnf.xz",
    "../data/sat2023/29505dfcf090c4cfdfb59268160be81d-hash_table_find_safety_size_24.cnf.xz",
    "../data/sat2023/29bab0de14e56e526be9683131005cb2-stb_588_138.apx_2_DS-ST.cnf.xz",
    "../data/sat2023/29e101b66dfddb440e974b9feec5b1aa-spg_200_307.cnf.xz",
    "../data/sat2023/2a144840047376cee3b7b99455158976-goldberg03:hard_eq_check:i10mul.miter.used-as.sat04-333.cnf.xz",
    "../data/sat2023/2a4680a801ad32ab8768030250daf0c8-ER_500_10_5.apx_2_DC-ST.cnf.xz",
    "../data/sat2023/2b3de92685792ae19e4549b5c4571e27-crafted_n12_d6_c4_num4.cnf.xz",
    "../data/sat2023/2b7e863462991fd008f9898eca63ebf4-SC23_Timetable_C_481_E_50_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/2c9dc96b7a8b0410e64dd33f7e00a0c1-30_2.cnf.xz",
    "../data/sat2023/2d0c041c0fe72dc32527bfbf34f63e61-170223547.cnf.xz",
    "../data/sat2023/2e808d215e4155379a847b146ef38b34-goldcrest-and-16.cnf.xz",
    "../data/sat2023/2ef023ae6c46e4415734f9349a36d678-velev-pipe-o-uns-1.0-7.cnf.xz",
    "../data/sat2023/2f219dfa21d996e1834aa247f934f304-grs-192-48.cnf.xz",
    "../data/sat2023/303ba61141150f84b0d8b44839df59fd-REGRandom-K3-L3-Seed10.cnf.xz",
    "../data/sat2023/30e680ded3b9be6be0b5baac273f2646-asconhashv12_opt64_H5_M2-A8qZX_m0_3_U23.c.cnf.xz",
    "../data/sat2023/323223c497a22051f5a3ef508ccbaa7c-SC23_Timetable_C_477_E_50_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/328da7966b09b2f6e99c93c4e877fbff-sgen3-n260-s62321009-sat.cnf.xz",
    "../data/sat2023/339b1cfda231aaca601cd6339c07ca2c-PRP_100_450.cnf.xz",
    "../data/sat2023/33bcf82677b7fdacf18dd48892596a1d-TimetableCNFEncoding_20_UNKNOWN.cnf.xz",
    "../data/sat2023/33cfa309d10e1d4fe30f1302807f42ce-SC23_Timetable_C_482_E_50_Cl_33_D_6_T_50.cnf.xz",
    "../data/sat2023/3498eea73b78ddc444cbee48b121c541-grs-64-160.cnf.xz",
    "../data/sat2023/34e5fd58b65bf305cc773f0dbfb47917-intervals553.cnf.xz",
    "../data/sat2023/358fa8d20aa467c7e9b9bf34f73d1dc9-patat-08-comp-3.cnf.xz",
    "../data/sat2023/35b19a3332597c1e5a3668f75ca72971-SC23_Timetable_C_480_E_50_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/361290e60ab2a8ea9dccfcff65bf0778-satcoin-genesis-UNSAT-9880.cnf.xz",
    "../data/sat2023/3663000b31a5c80922afc6e48322accb-6s165.cnf.xz",
    "../data/sat2023/36c342091848d5d6a1a8eeb3a8b49b86-rovers1_ks99i.renamed-as.sat05-3971.cnf.xz",
    "../data/sat2023/3728fe50d8038c639c2d9c84e04fe2b1-46bits_11.dimacs.cnf.xz",
    "../data/sat2023/37d40a1092b58ad28285b9453872d211-DecompressReader_read_12.cnf.xz",
    "../data/sat2023/385a678ba820d79c6fb5f497adaf32ec-grs-48-128.cnf.xz",
    "../data/sat2023/385e2c7010a419a9bd47b9258c9d2903-tseitin_d3_n200.cnf.xz",
    "../data/sat2023/38833d6a1ff6a56ef22bd2dc1e3fdde7-rbsat-v1150c84314gyes10.cnf.xz",
    "../data/sat2023/38ca761a5808eace8bc8f1fcfdb5b5a8-multiplier_15bits__miter_20.cnf.xz",
    "../data/sat2023/396245861b331d45e1345bd43fe352e2-asconhashv12_opt64_H8_M2-1yQCyA0j_m2_6.c.cnf.xz",
    "../data/sat2023/3a7a64e1d6cf5ce969b2b05b5464f707-PRP_30_38.cnf.xz",
    "../data/sat2023/3cff6c97a515aecfe46ba0f1256a3c11-shuffling-1-s1870372346-of-bench-sat04-423.used-as.sat04-562.cnf.xz",
    "../data/sat2023/3e7dc7350195104b76b7d03ab5b0af8f-SC23_Timetable_C_490_E_50_Cl_33_D_6_T_50.cnf.xz",
    "../data/sat2023/3f341c57c37d86350af5233b8e15e52e-19_2.cnf.xz",
    "../data/sat2023/3f4174289e971950c290f27892169bc5-intervals607.cnf.xz",
    "../data/sat2023/3ff114cc7bee4f39fa56a0325e605c2d-stb_588_138.apx_2_DC-ST.cnf.xz",
    "../data/sat2023/4029fbae284eaf924b37b6f43d3a67fb-WCNF_from_fp_14.cnf.xz",
    "../data/sat2023/40ae60a61929b6bfa2ac99ab4b9a0f7e-grs-96-192.cnf.xz",
    "../data/sat2023/41457ee03686b32962c12445524f62a9-mchess18-mixed-45percent-blocked.cnf.xz",
    "../data/sat2023/41a8365f60db55b71d949df6954e0db7-FileObject_open_13.cnf.xz",
    "../data/sat2023/41c39c9a2d75ca50b603ea7c3d86106a-brent_63_0.cnf.xz",
    "../data/sat2023/4282ea42fd414bfd2c4bf81fe8a43e24-DivU_1520_10.cnf.sanitized.cnf.xz",
    "../data/sat2023/428da12ab8f5f68ae261e6468c2fef73-TableSymModel_output_8_3_10.bul_.dimacs.cnf.xz",
    "../data/sat2023/431bfb466be51ecd86b321b5cbce6d3c-mrpp_8x8#22_10.cnf.xz",
    "../data/sat2023/4380f8ed143d97a65f8888b2feeddb80-intervals477.cnf.xz",
    "../data/sat2023/4408f30395fb799e01b34b0dc7ee1d62-cliquecoloring_n14_k9_c8.cnf.xz",
    "../data/sat2023/44092fcc83a5cba81419e82cfd18602c-php-010-009.shuffled-as.sat05-1185.cnf.xz",
    "../data/sat2023/44ad104c3b0c83b4cfc260583dee2397-PRP_30_36.cnf.xz",
    "../data/sat2023/44b249f51321a2bf38f730534b781bec-c880_gr_rcs_w7.shuffled.cnf.xz",
    "../data/sat2023/45faf223af97fe9177daa3ad4002cf2f-hash_table_find_safety_size_25.cnf.xz",
    "../data/sat2023/4611cd26b441b8c5866e4a2c5a7952dc-WS_400_24_90_10.apx_1_DS-ST.cnf.xz",
    "../data/sat2023/46e119b7ff8d0781354bfe68139c99b5-grs-96-96.cnf.xz",
    "../data/sat2023/48539e7e4baae6db72cda7e8a9cecfa0-oisc-subrv-sll-nested-15.cnf.xz",
    "../data/sat2023/48ac8814180bdc90bf96a4caea64dae2-intervals633.cnf.xz",
    "../data/sat2023/4989239fbeb6eb40fc0b664d9ba92636-asconhashv12_opt64_H7_M2-K1zfAs8_m0_3_U5.c.cnf.xz",
    "../data/sat2023/4a6a797c6b4a8055d10b74edda9a5e30-TableSymModel_output_8_4_8.bul_.dimacs.cnf.xz",
    "../data/sat2023/4d2f74ef97b6d40ebd71f85dcb75c543-tseitingrid7x160_shuffled-sc2016.cnf.xz",
    "../data/sat2023/4e64ffc14db014d5591f40865376c32a-satcoin-genesis-UNSAT-7200.cnf.xz",
    "../data/sat2023/4f38f4b005cc54122135c8c21aec4b85-intervals7.cnf.xz",
    "../data/sat2023/4fd2e4e6ecb4fe8d3f9e1fda81633469-brent_69_0.05.cnf.xz",
    "../data/sat2023/4fdcf4248a332c1c9a89d37439c879a9-or_randxor_k3_n520_m520.cnf.xz",
    "../data/sat2023/4fe42891b004d7425631a8edb4252d3f-32_0.cnf.xz",
    "../data/sat2023/4ffb80a0ad8b753fee1492101ffcbdbb-REGRandom-K4-L1-Seed5.cnf.xz",
    "../data/sat2023/524848d379582b63060ed43d3729b9f3-satcoin-genesis-UNSAT-19500.cnf.xz",
    "../data/sat2023/52be8740aab896317320cd44a5d2af2f-intervals753.cnf.xz",
    "../data/sat2023/53799aafcd0c684a2adc79400bd35f82-satcoin-genesis-UNSAT-5920.cnf.xz",
    "../data/sat2023/5437ba8972228ea5531a69a9aa064acc-satcoin-genesis-UNSAT-19800.cnf.xz",
    "../data/sat2023/54ab5a53d2fdfcda16ec74768b29f901-rphp_p30_r30.cnf.xz",
    "../data/sat2023/558113ad4d50130351db8c426230a50f-asconhashv12_opt64_H9_M2-wNfQskE8G_m1_6_U0.c.cnf.xz",
    "../data/sat2023/558ce551d2b933b7a5f1c7d2a6044930-collections_namedtuple_15.cnf.xz",
    "../data/sat2023/571a2f223784fb92a53b4cc8cc8b569e-clqcolor-08-06-07.shuffled-as.sat05-1257.cnf.xz",
    "../data/sat2023/578b5e6a2f0b295168cb6c5420810a72-php18-mixed-35percent-blocked.cnf.xz",
    "../data/sat2023/578f9377bfbfcc6ea3a18eb630667956-ferry8_ks99i.renamed-as.sat05-4005.cnf.xz",
    "../data/sat2023/57c305967b30c503da1737258e6cc7e5-6s20-sc2013.cnf.xz",
    "../data/sat2023/587150fb7b12a6b5dd7e4a9446b9713b-iso-ukn004.shuffled-as.sat05-3385.cnf.xz",
    "../data/sat2023/5918f1624d4dfd964227356786a4e9ec-ContextModel_output_8_4_9.bul.dimacs.cnf.xz",
    "../data/sat2023/5a72cb588bcda7b1b54a1eac6b19ab2e-hash_table_find_safety_size_23.cnf.xz",
    "../data/sat2023/5b3d8a4465726adfcb58b9cdb1cc33f1-intervals222.cnf.xz",
    "../data/sat2023/5dc5185101e1d439d14f0a04acfa9bfb-28_2.cnf.xz",
    "../data/sat2023/5f6861053fb4ed4fc0b997cd6b505ef4-tseitin_d3_n110000.cnf.xz",
    "../data/sat2023/62c763bdf8d351b15df3a4d62a03eba0-g2-ak128astepbg2asisc.cnf.xz",
    "../data/sat2023/63159b6b10c3d6832bd5944e05d78b11-SCPC-700-80.cnf.xz",
    "../data/sat2023/644fd765d26bd4a380922ccd0f594c58-mchess18-mixed-25percent-blocked.cnf.xz",
    "../data/sat2023/6549f23728c52d5319f30371ff709622-hash_table_find_safety_size_27.cnf.xz",
    "../data/sat2023/65b1e2253626af4a72b954f8186a5880-hash_table_find_safety_size_10.cnf.xz",
    "../data/sat2023/670a24d73dbadd3073e9604c6ef903d1-tseitin_grid_n260_m260.cnf.xz",
    "../data/sat2023/67904554c73addf89fe675bd8e494641-intervals327.cnf.xz",
    "../data/sat2023/67a5b7ccde980b37576b993c79e176b0-hash_table_find_safety_size_22.cnf.xz",
    "../data/sat2023/685d37e93ba26197925353e58026ae10-hash_table_find_safety_size_12.cnf.xz",
    "../data/sat2023/68649ac2830edad5d0dc7e3d13935132-SCPC-800-46.cnf.xz",
    "../data/sat2023/6aacae96461cb65176942b6dc88ea470-mchess20-mixed-25percent-blocked.cnf.xz",
    "../data/sat2023/6b2ccabf0304af478a558b8a333ced32-grs-192-256.cnf.xz",
    "../data/sat2023/6bb485770dbc3943ea84933a03131958-satcoin-genesis-UNSAT-18600.cnf.xz",
    "../data/sat2023/6d67f76f114db9801952ed155e745e16-23_2.cnf.xz",
    "../data/sat2023/6dca14e1af1795565d1e502ddc7d376b-hash_table_find_safety_size_15.cnf.xz",
    "../data/sat2023/6e31e88a5dadaa3876eb5ff4293134c2-hash_table_find_safety_size_21.cnf.xz",
    "../data/sat2023/6e5efd19744842d1fa5415173bffbf6b-tseitin_d3_n180000.cnf.xz",
    "../data/sat2023/6e9cae5108bd423666c73aaace197769-brent_51_0.28.cnf.xz",
    "../data/sat2023/705f6075b27775e03daf6e8d781cb953-shift1add.28943.cnf.xz",
    "../data/sat2023/70af2c3bfd44bcf9baa2a9605f4a17fe-gensys-icl002.shuffled-as.sat05-2714.cnf.xz",
    "../data/sat2023/70ce0cff914efdc48f2a8fe86b5c68c6-TableModel_output_8_4_7.bul_.dimacs.cnf.xz",
    "../data/sat2023/711ff7681711949f44b07a0d530dc729-asconhashv12_opt64_H12_M2-CxLJidFX21oI_m3_6_U2.c.cnf.xz",
    "../data/sat2023/71270454196ae092b28d0a74300a85e1-Schur_161_5_d40.cnf.xz",
    "../data/sat2023/71758ed7637888d4fd4593ec820677bc-SCPC-800-42.cnf.xz",
    "../data/sat2023/71bca76153c6ee65b72a517fd658a42d-iso-brn100.shuffled-as.sat05-3025.cnf.xz",
    "../data/sat2023/71cf538aa0751d27f144de9c8d82e458-TableModel_output_8_3_10.bul_.dimacs.cnf.xz",
    "../data/sat2023/71dbf7ab78ef93c3d491c67752f03fd1-hwmcc10-timeframe-expansion-k45-nusmvguidancep9-tseitin.cnf.xz",
    "../data/sat2023/727cd7c528ac106f134cc882c9202108-15pipe_q0_k.cnf.xz",
    "../data/sat2023/72b5ad031bf852634bc081f9da9a5a60-GzipFile_close_11.cnf.xz",
    "../data/sat2023/73063c6257a4ffc29f5bea7028403a64-mod2c-rand3bip-sat-250-2.shuffled-as.sat05-2534.cnf.xz",
    "../data/sat2023/74931e82fd208ed949fa44bccd80df6b-DivS_862_11.cnf.sanitized.cnf.xz",
    "../data/sat2023/751402d0738e5622b599c651283cb48a-SCPC-800-43.cnf.xz",
    "../data/sat2023/751afd7ddf8f242ed7bd93517ba82149-mchess20-mixed-45percent-blocked.cnf.xz",
    "../data/sat2023/758f9ed67b4d2068c209157335e07266-or_randxor_k3_n640_m640.cnf.xz",
    "../data/sat2023/78d23f235b63b1b7f08eb1b6cfb03f34-29_1.cnf.xz",
    "../data/sat2023/79391ed5a7f19b947cefe7af1178146a-21_1.cnf.xz",
    "../data/sat2023/79c109a8c1da53c6b636d3835f11a19d-grs-64-32.cnf.xz",
    "../data/sat2023/7aaf3275cbe217044ef305f0a1ca8eb5-CNFPlus_from_fp_12.cnf.xz",
    "../data/sat2023/7b4622a3ab523264378a560199de47ed-ER_400_20_4.apx_1_DC-ST.cnf.xz",
    "../data/sat2023/7d58f2f0c79cbcad0496ced184ba0680-TableSymModel_output_6_3_8.bul_.dimacs.cnf.xz",
    "../data/sat2023/7dc81d3cb9066f8bc06ceffbca237572-TableModel_output_7_3_9.bul_.dimacs.cnf.xz",
    "../data/sat2023/81d2158d506ea1049708837460b9387e-WS_400_24_70_10.apx_2_DC-AD.cnf.xz",
    "../data/sat2023/824c21545e228872744675ae4ee32976-WCNFPlus_to_alien_14.cnf.xz",
    "../data/sat2023/8252d67358381873e07bb637ad177b83-hash_table_find_safety_size_16.cnf.xz",
    "../data/sat2023/8270ae50e6f2881136868db6d3a88eee-WS_400_24_90_10.apx_2_DC-AD.cnf.xz",
    "../data/sat2023/828e1066a477e98e8d834528df3fc874-or_randxor_k3_n560_m560.cnf.xz",
    "../data/sat2023/82fe0a5b2467d6e5299c315da8b16ec5-brent_51_0.07.cnf.xz",
    "../data/sat2023/835ac60ca83af6f334b64b61c4ad345b-tseitin_d3_n160.cnf.xz",
    "../data/sat2023/83cf6bfa7945b54e8c4ac659d1a4359e-SC23_Timetable_C_473_E_52_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/8403d03df1ce64af3bf7581449d320fb-brent_63_0.26.cnf.xz",
    "../data/sat2023/85240babab8083e1b381e2971d875ab8-satcoin-genesis-UNSAT-17800.cnf.xz",
    "../data/sat2023/8751f8d1570611ba079dfd862b14c514-SC23_Timetable_C_473_E_49_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/87ec32f70c5e3a279e636f7f62e70a19-mchess22-mixed-45percent-blocked.cnf.xz",
    "../data/sat2023/89120de895868a3fccd74f30f78a5448-grs-192-160.cnf.xz",
    "../data/sat2023/8a7a61a63a718e4dc5aba5426b31c063-satcoin-genesis-UNSAT-18400.cnf.xz",
    "../data/sat2023/8ade10da9731ce31d103c1687ff40a3d-brent_63_0.15.cnf.xz",
    "../data/sat2023/8b797110ff321ee673eab1542069f192-ContextModel_output_8_4_10.bul.dimacs.cnf.xz",
    "../data/sat2023/8bcd3f3e269fa3c9516667b626d61602-TableSymModel_output_8_4_7.bul_.dimacs.cnf.xz",
    "../data/sat2023/8c7477dc33a412514998a2fd6b32dbf5-intervals855.cnf.xz",
    "../data/sat2023/8cf6b81061285343c4f33c51afdb3fbb-minxor128.cnf.xz",
    "../data/sat2023/8cfc8e99d31bcaf18ff3360b08c8521c-sat-bench-trig-taylor6.cnf.xz",
    "../data/sat2023/8d31ec9edeac705ffd1b23f0cc4f3256-ContextModel_output_7_3_9.bul_.dimacs.cnf.xz",
    "../data/sat2023/8d458780fb74c28c01a5fe89990ad521-mchess16-mixed-45percent-blocked.cnf.xz",
    "../data/sat2023/8db36208fc6ce43b4002cf048c549b3f-WS_400_32_90_10.apx_1_DC-AD.cnf.xz",
    "../data/sat2023/8e30bfdb721ca0a20031c79a76f9aa7c-satcoin-genesis-UNSAT-18800.cnf.xz",
    "../data/sat2023/8f7cd9fb4b8852fdf9a21c606724c71a-satcoin-genesis-UNSAT-12300.cnf.xz",
    "../data/sat2023/8fa526d20599ca8c3d613e9066d62e61-sat-bench-trig-taylor2.cnf.xz",
    "../data/sat2023/8fcc57f6c75cb2ac48d19e3038ad3c6c-asconhashv12_opt64_H6_M2-4XKSMr_m1_3_U25.c.cnf.xz",
    "../data/sat2023/909f704d5f4127c1197a086705468624-rbsat-v760c43649gyes10.cnf.xz",
    "../data/sat2023/911cbc796d15eb316d36c82c90fd7d11-c499_gr_2pin_w6.shuffled.cnf.xz",
    "../data/sat2023/91b88d172a08e2a57c189bddff51bfd5-22_1.cnf.xz",
    "../data/sat2023/92387c29e87aa857e84feb301f3d6aff-rbsat-v760c43649gyes5.cnf.xz",
    "../data/sat2023/92c17c00d862668de6e6c45d4eecdc75-combined-crypto1-wff-seed-101-wffvars-500-cryptocplx-31-overlap-2.cnf.xz",
    "../data/sat2023/92d6795785d35d1dcc42b15dc0e933d0-grid-pbl-0150.shuffled-as.sat05-1347.shuffled-as.sat05-1347.cnf.xz",
    "../data/sat2023/93a87994c03a7752f85d863239555d48-PRP_30_35.cnf.xz",
    "../data/sat2023/945d67baeb7860df648ab6ef4782d5ed-stb_792_333.apx_1_DS-ST.cnf.xz",
    "../data/sat2023/953e9ff735bdf5ada27b0ab2b908b6af-WS_400_24_70_10.apx_1_DC-ST.cnf.xz",
    "../data/sat2023/9631e4082abf03e560b889c5715d3979-PRP_30_41.cnf.xz",
    "../data/sat2023/964162c1faee2c1e3a4dfa4f9c75c34f-php18-mixed-15percent-blocked.cnf.xz",
    "../data/sat2023/965ca988015c9aee5a1a7b2136c1fe5d-os_fwalk_12.cnf.xz",
    "../data/sat2023/96ae6bde39369f75aa975b0f5b74c325-asconhashv12_opt64_H13_M2-NBRdIKEb8MS2W_m3_5.c.cnf.xz",
    "../data/sat2023/96e01064ac3b644143278c21859e201f-brent_51_0.29.cnf.xz",
    "../data/sat2023/97a17306a2882e0fd1aa3981a267df0d-SC23_Timetable_C_473_E_46_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/9811b95bfd5888014d27e6dd384ff502-WS_500_16_90_70.apx_2_DC-ST.cnf.xz",
    "../data/sat2023/98c6da979a0a22d384d465a1da17111e-PRP_100_250.cnf.xz",
    "../data/sat2023/99d134de6323a845a2828596a48bbb1d-php17-mixed-15percent-blocked.cnf.xz",
    "../data/sat2023/9a413c250f82a93d513d4092ba654ee2-asconhashv12_opt64_H4_M2-ldRf_m1_2_U21.c.cnf.xz",
    "../data/sat2023/9c7043290cee8127c3626d8067759267-stb_531_83.apx_2_DC-AD.cnf.xz",
    "../data/sat2023/9de6ddddf7fde06bf2efd955e2bd1a83-SCPC-700-84.cnf.xz",
    "../data/sat2023/9e18c079efdc17ceade5c7a330b507d2-SC23_Timetable_C_474_E_50_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/9e7f2b92c6e46d03ddcafd798aa80cb6-hash_table_find_safety_size_17.cnf.xz",
    "../data/sat2023/9f3ef12b5b68f92eb9265721ea73bb03-asconhashv12_opt64_H9_M2-Jdds95CIv_m1_5.c.cnf.xz",
    "../data/sat2023/9fe43145e48a0ef0096bb72531f1a0e3-16_1.cnf.xz",
    "../data/sat2023/a09a2d7397732447bdcc9651973767b7-TableSymModel_output_6_5_6.bul_.dimacs.cnf.xz",
    "../data/sat2023/a0c7aea176b5a2b65c27c8af7039326b-grs-160-64.cnf.xz",
    "../data/sat2023/a1276d5dcb822aa03806df58fa9ca1c8-grs-128-32.cnf.xz",
    "../data/sat2023/a18b6fbdfee43c007e07dedf15477797-SCPC-700-86.cnf.xz",
    "../data/sat2023/a292411f3f563a47c05a78f8295163dc-hash_table_find_safety_size_26.cnf.xz",
    "../data/sat2023/a45b60e53917968f922b97c6f8aa8db3-unsat-set-b-fclqcolor-10-07-09.sat05-1282.reshuffled-07.cnf.xz",
    "../data/sat2023/a4941208671f6ebfd118e4e563538c31-SCPC-1000-20.cnf.xz",
    "../data/sat2023/a4b05fbc5be28207b704e1fae4b7c8a0-FileObject_open_12.cnf.xz",
    "../data/sat2023/a552a058e6376a36b1f1b2724f228364-IBM_FV_2004_rule_batch_1_31_1_SAT_dat.k40.debugged.cnf.xz",
    "../data/sat2023/a64f3c1afd7e0f6165efbe9fc2fc8003-pmg-12-UNSAT.sat05-3940.reshuffled-07.cnf.xz",
    "../data/sat2023/a6d7268b35eec18656a85ad91b0413e9-php17-mixed-35percent-blocked.cnf.xz",
    "../data/sat2023/a7a9ca7e06b6b1e979950ea96183d07d-rook-47-0-1.cnf.xz",
    "../data/sat2023/a7bbcc6535cca5a37f015f29090e8797-grs-48-256.cnf.xz",
    "../data/sat2023/a811388cc92def6ef2d639dc062d456c-ContextModel_output_6_3_8.bul_.dimacs.cnf.xz",
    "../data/sat2023/a83665715cf54e10f6d5382b97fd909c-PRP_100_400.cnf.xz",
    "../data/sat2023/a8dc92a9c0434576b47c82c94ab5c446-Grain_no_init_ver1_out200_known_last105_0_u.cnf.xz",
    "../data/sat2023/a8dcaf436bda091dad9ca1ff58de7287-asconhashv12_opt64_H10_M2-BPHqhzNzqi_m5_6_U14.c.cnf.xz",
    "../data/sat2023/a931fb0e1490883ee7719eab96ed558a-T87.2.0.cnf.xz",
    "../data/sat2023/a98d77ba9d3fbe8b7c55cbf75b2b43a8-TableModel_output_6_3_8.bul_.dimacs.cnf.xz",
    "../data/sat2023/a9d081cbb33e6051be2512f2a2269d65-hash_table_find_safety_size_20.cnf.xz",
    "../data/sat2023/aa0d6b8c63f57956b9aed350f38e0571-intervals244.cnf.xz",
    "../data/sat2023/aa4a861240c0c39b5aa44602133ae5e1-stb_418_125.apx_2_DC-ST.cnf.xz",
    "../data/sat2023/abe802007c9aed4eab2e758fb130174b-mp1-klieber2017s-1600-022-eq.cnf.xz",
    "../data/sat2023/accf33a84bdf211bebbd2111fb7f6b91-DivS_942_11.cnf.sanitized.cnf.xz",
    "../data/sat2023/ad69e0a0880cd377e26260f7e4bc6d51-g2-T49.2.0.cnf.xz",
    "../data/sat2023/ae7e391be73431e5dddf2bbafe95758a-WS_400_24_70_10.apx_2_DC-ST.cnf.xz",
    "../data/sat2023/ae9522ea003ea9f75891b2d37a5e264b-srhd-sgi-m37-q446.25-n35-p30-s33692332.cnf.xz",
    "../data/sat2023/ae9b7950ef1513068bb9339893ec8c50-WCNF_to_alien_14.cnf.xz",
    "../data/sat2023/af1e84bc2ab44d87d1c4c0cbf9e601c5-posixpath_expanduser_14.cnf.xz",
    "../data/sat2023/af3d5273605b21b9d4c56dd46cbf366a-SCPC-700-82.cnf.xz",
    "../data/sat2023/af5838e83024d2dee3942be8d8e35fec-TableModel_output_8_4_8.bul_.dimacs.cnf.xz",
    "../data/sat2023/b09585f2346c207e9e14a3daf0de46cf-CNF_to_alien_11.cnf.xz",
    "../data/sat2023/b157aeb75aec9158fed9e16d7fd2da57-ContextModel_output_6_4_6.bul_.dimacs.cnf.xz",
    "../data/sat2023/b2145c28dbed385329ea73a06d9c519a-LZMAFile___init___14.cnf.xz",
    "../data/sat2023/b3840e295097a13e6697fff6be813eeb-php16-mixed-15percent-blocked.cnf.xz",
    "../data/sat2023/b44611ea7852dd30215cc1cb09e1ab79-PRP_30_39.cnf.xz",
    "../data/sat2023/b5b1803491a265b02d595c1fb62d5991-intervals802.cnf.xz",
    "../data/sat2023/b5cede38496a803dcfa155a5f4295c47-SC23_Timetable_C_476_E_50_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/b6c44ccb3174b7f0a69185b11de86cfa-grs-128-64.cnf.xz",
    "../data/sat2023/b6c6f1081dbb672e8294685d03326b09-intervals80.cnf.xz",
    "../data/sat2023/b86f2425cafeb1239d65bd529e372e02-ER_500_10_1.apx_1_DC-AD.cnf.xz",
    "../data/sat2023/bab57c8799cb05c8c1757c60d4ebdefd-satcoin-genesis-UNSAT-17400.cnf.xz",
    "../data/sat2023/bb8042839130ce5597c358c1955706ff-hash_table_find_safety_size_30.cnf.xz",
    "../data/sat2023/bbf800109d039e117ed60593c185692c-ER_500_10_2.apx_1_DS-ST.cnf.xz",
    "../data/sat2023/bc3a8bd47c5575c2f1b31882d28ee091-26_1.cnf.xz",
    "../data/sat2023/bc7dc7a83b442a2bf4cf8cae3f0e0faa-hash_table_find_safety_size_18.cnf.xz",
    "../data/sat2023/bca01a49805df3399a0438191019e417-SCPC-700-87.cnf.xz",
    "../data/sat2023/bcd753d08904860fa93a794557185e04-SC23_Timetable_C_488_E_50_Cl_33_D_6_T_50.cnf.xz",
    "../data/sat2023/bd0b055b890a9ace598a0c4aba40de30-sat-bench-trig-bhaskara.cnf.xz",
    "../data/sat2023/bdc85226a8d910a8b7d6a8730c7a4572-PRP_40_40.cnf.xz",
    "../data/sat2023/be5c82b97513a31e0b3bcc1c231018ad-asconhashv12_opt64_H15_M2-kwhXs2juqFoKAYA_m12_13_U16.c.cnf.xz",
    "../data/sat2023/c0069efa0c924e416878d9426f1ef92e-SCPC-900-29.cnf.xz",
    "../data/sat2023/c115ebeec47bb82fa7f9850a632ec94a-brent_71_0.25.cnf.xz",
    "../data/sat2023/c1324a6876269ee93890e266fe214557-SCPC-800-50.cnf.xz",
    "../data/sat2023/c1b5c3d1016de7baeb0ddb3a2ab2d891-SCPC-900-27.cnf.xz",
    "../data/sat2023/c32f194ad850c944142c74514dfb3c5f-WCNFPlus_from_fp_13.cnf.xz",
    "../data/sat2023/c40838cb3ed9babe51dc41185e70a3dd-hash_table_find_safety_size_11.cnf.xz",
    "../data/sat2023/c7bf3517f47d583ae567de3db3708969-oisc-subrv-and-nested-14.cnf.xz",
    "../data/sat2023/c9af5b23c87350f5d817acc9ca7b69bb-CNF_to_alien_12.cnf.xz",
    "../data/sat2023/c9f7ca549a6773bea4628e2c66f597c6-brent_51_0.17.cnf.xz",
    "../data/sat2023/caead0e04b6de4365822b25dfd55967f-preimage_80r_490m_160h_seed_150.cnf.xz",
    "../data/sat2023/cbd0933002d6c4ea99ceb47bb0c3f4c9-em_11_3_4_cmp.cnf.xz",
    "../data/sat2023/cd118ff851f95661b2a3adfc3e393c74-Schur_160_5_d34.cnf.xz",
    "../data/sat2023/cd58fa8eba4046fd0a86642e1fe26cb9-intervals803.cnf.xz",
    "../data/sat2023/cd86fbfd8b7e0d66ec5fe8fe85c014d3-mchess22-mixed-35percent-blocked.cnf.xz",
    "../data/sat2023/cdd131110acc861a5a01fae6c4936c91-6g_6color_366_050_04.cnf.xz",
    "../data/sat2023/ce49f590c98885f7ac95567f2b1e7dd5-CNP-5-1100.cnf.xz",
    "../data/sat2023/cea96962ebd736646af54d950943d909-SCPC-800-41.cnf.xz",
    "../data/sat2023/cfc53adcc8ed18ca161bb6f8bc02b237-asconhashv12_opt64_H7_M2-gHvzZOd_m3_4_U11.c.cnf.xz",
    "../data/sat2023/d0364ea3e1680c6da7e982e6b0264af6-new-difficult-26-243-24-70.cnf.xz",
    "../data/sat2023/d0fe6bf914469ca51675bac9078a2c0b-asconhashv12_opt64_H10_M2-pH7B6T6Vub_m6_7.c.cnf.xz",
    "../data/sat2023/d17aa530bbd09452b0f32daf4ab9c8f0-tph8.cnf.xz",
    "../data/sat2023/d1a62a8688c6c4fabd0dec3770ce40dd-qwh.40.560.shuffled-as.sat03-1654.cnf.xz",
    "../data/sat2023/d1f4348ad66cae01386777daae51c024-eqspctbk14spwtcl14.cnf.xz",
    "../data/sat2023/d3529338d35aa27e8024932d3b5f64b5-PRP_20_50.cnf.xz",
    "../data/sat2023/d3daba681653ea969bedf0c4a2fdb947-ER_400_20_7.apx_1_DC-ST.cnf.xz",
    "../data/sat2023/d46c3fc9e953d4f84e8a18e52e29e7b7-PRP_100_350.cnf.xz",
    "../data/sat2023/d5efaaee0197822c2676e45bac5068b2-SC23_Timetable_C_484_E_50_Cl_33_D_6_T_50.cnf.xz",
    "../data/sat2023/d60f56735dc8e89d7d91a01f4340df0c-baseballcover13with25_and3positions.cnf.xz",
    "../data/sat2023/d6402b482a5dc102a5b09360689e2be8-jkkk-one-one-11-32-unsat.cnf.xz",
    "../data/sat2023/d66ab8bce1b8979dbd26b3c220e817be-PRP_200_100.cnf.xz",
    "../data/sat2023/d7f381cd99ca40ba3324c8cc03a54269-mchess16-mixed-25percent-blocked.cnf.xz",
    "../data/sat2023/d84a89fb1bc1ff37dc4737867257b290-SCPC-800-49.cnf.xz",
    "../data/sat2023/d89718e39ff99638c2882b47988120cd-brent_63_0.1.cnf.xz",
    "../data/sat2023/d89f0a7a08f9b60579b26b01e2196394-intervals467.cnf.xz",
    "../data/sat2023/d8f131a86243ef138af39abf52a479e5-SC23_Timetable_C_481_E_51_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/d8fa4265b93d0931ba6484e3cc0d7ab1-brent_13_0.1.cnf.xz",
    "../data/sat2023/da43a3ef0ef5d34143e765d480dedc7a-DivU_624_11.cnf.sanitized.cnf.xz",
    "../data/sat2023/db4a0d4ba26c46d66ad6cdcb0645a4d9-WS_500_16_70_10.apx_2_DC-ST.cnf.xz",
    "../data/sat2023/dbe18c99e95ac42816b99b96d36a8732-grs-32-256.cnf.xz",
    "../data/sat2023/dd169198070f9aa35015de65e8209a05-LZMAFile_write_12.cnf.xz",
    "../data/sat2023/dd6ef995af0267ce71076250a1226801-intervals313.cnf.xz",
    "../data/sat2023/ddd3b43476c18cf483aac233d4dc1c68-PRP_20_40.cnf.xz",
    "../data/sat2023/deef4e5f8bf88393cea9589dff97d70c-ContextModel_output_8_4_8.bul_.dimacs.cnf.xz",
    "../data/sat2023/df237594dc22b8f7cad2c4b38a23e40c-17_0.cnf.xz",
    "../data/sat2023/e444548857eaf649c4624e3494c89c8e-asconhashv12_opt64_H8_M2-bL4cM6NJ_m4_5_U14.c.cnf.xz",
    "../data/sat2023/e46bdd62b3789b64f7fbb3bd6c99484e-intervals727.cnf.xz",
    "../data/sat2023/e51a98d78f61103e0672579e87cfd7e5-satcoin-genesis-UNSAT-11400.cnf.xz",
    "../data/sat2023/e5a72ac8f4880702a4deacc7854318e8-hash_table_find_safety_size_19.cnf.xz",
    "../data/sat2023/e6d247292b525447a220323901842e4c-or_randxor_k3_n540_m540.cnf.xz",
    "../data/sat2023/e966bddd11e46b735f8520f8304e368e-SC23_Timetable_C_483_E_50_Cl_33_D_6_T_50.cnf.xz",
    "../data/sat2023/ea5b47b3ffb3b8cb77a2cff83cc1ffba-PRP_100_500.cnf.xz",
    "../data/sat2023/eaf2f0803dd2045f1b189ee834ef0c8f-rphp_p8_r250.cnf.xz",
    "../data/sat2023/eca3692344e30ae83a49158b5baf3372-brent_65_0.1.cnf.xz",
    "../data/sat2023/ed76b075cdf07435c6e4f6203dd10cb7-SCPC-700-88.cnf.xz",
    "../data/sat2023/eec821f866557886a5b0352332943fa2-SCPC-700-81.cnf.xz",
    "../data/sat2023/eecdcc36d35f06224cc972cbb08de804-SCPC-1000-18.cnf.xz",
    "../data/sat2023/f02379d63678798e38dcc52b043cc51d-asconhashv12_opt64_H13_M2-axxJh7DAq767y_m4_5.c.cnf.xz",
    "../data/sat2023/f0895a5904fb97278b7b54733ee1dabb-brent_63_0.22.cnf.xz",
    "../data/sat2023/f08b3567642ea029452fff2c1d10c132-brent_15_0.25.cnf.xz",
    "../data/sat2023/f090d0d6eaff3b92c817f5db6fa47544-intervals718.cnf.xz",
    "../data/sat2023/f20c2aa0f9cced05a74031e0a3afaa1a-SC23_Timetable_C_473_E_50_Cl_32_D_6_T_50.cnf.xz",
    "../data/sat2023/f26f199564d6ffac7e700c2e66470ec0-TableSymModel_output_6_4_6.bul_.dimacs.cnf.xz",
    "../data/sat2023/f35ed23733431177436a1e7797c07dfe-SCPC-900-31.cnf.xz",
    "../data/sat2023/f4064d73fd6e69caf154046e61fea7b8-cliquecoloring_n18_k7_c6.cnf.xz",
    "../data/sat2023/f448874997bae64bd455fb00309dc738-asconhashv12_opt64_H7_M2-OrF8zEw_m2_4.c.cnf.xz",
    "../data/sat2023/f55acea8f0d207becbbbd26a11d97841-grs-48-160.cnf.xz",
    "../data/sat2023/f57aba96bfed8f8a8b860eba1a8f1ea5-TableModel_output_6_4_6.bul_.dimacs.cnf.xz",
    "../data/sat2023/f88afbcd8b4c29a8c1b3518caa4e949c-cliquecoloring_n16_k7_c6.cnf.xz",
    "../data/sat2023/f959755d7c68ea8b64d900e589fbe21f-g2-slp-synthesis-aes-top29.cnf.xz",
    "../data/sat2023/fab0db1ab0dd5baa3215aab51ab69355-brent_63_0.2.cnf.xz",
    "../data/sat2023/faeb113864d97ea4cb3f01f95d2fe92f-SCPC-800-44.cnf.xz",
    "../data/sat2023/fb5d0254bc4b8d258eb84ea1dbcdda13-mchess22-mixed-25percent-blocked.cnf.xz",
    "../data/sat2023/fd1fbc1b090c14746a883b3a17259743-9vliw_bp_mc.shuffled.cnf.xz",
    "../data/sat2023/fd2af7622798171f23a4b8d2616df55e-StreamReader_readline_13.cnf.xz",
    "../data/sat2023/fdc5aa7c150fd1c49ad3b50433277528-PRP_100_300.cnf.xz",
    "../data/sat2023/fdfcd52a21824b7181d66672f283ba04-instance_n6_i6_pp_ci_ce.cnf.xz",
    "../data/sat2023/fe19a31b76cbba5901e16ce36c7578ed-C208_FA_UT_3254.cnf.xz",
    "../data/sat2023/fe8b1ef742724947620a419d0180a640-mchess18-mixed-35percent-blocked.cnf.xz",
    "../data/sat2023/fee70cede2b5b55bfbdb6e48fbe7ce4f-DLTM_twitter690_74_16.cnf.xz",
    "../data/sat2023/ff5170c690129f8c94658e82b6aab05c-Urquhart-s5-b4.shuffled.cnf.xz",
    "../data/sat2023/ff867fd35aa52058382a8b0c21cd1f38-mchess20-mixed-35percent-blocked.cnf.xz",
)

TIMEOUT = float(sys.argv[1])


class TimeoutError(Exception):
    def __str__(self):
        return "TimeoutError"


class ReturnCodeError(Exception):
    def __init__(self, returncode):
        self.returncode = returncode

    def __str__(self):
        return f"ReturnCode{self.returncode}"


class NotFoundError(Exception):
    def __str__(self):
        return "NotFound"


async def check_stdin_unpacked(problem, program) -> Union[bytes, Exception]:
    try:
        with open(problem, "r") as f:
            p = await asyncio.create_subprocess_exec(
                program,
                stdin=f,
                stdout=asyncio.subprocess.PIPE,
            )

            assert p.stdout is not None
            try:
                result = await asyncio.wait_for(p.stdout.read(), TIMEOUT)

                # check status code
                if await p.wait() not in (0, 10, 20):
                    return ReturnCodeError(p.returncode)

                return result
            except asyncio.TimeoutError:
                p.terminate()
                return TimeoutError()
    except FileNotFoundError:
        return NotFoundError()


def unxz(problem):
    with open(problem, "r") as f:
        with open("../data/unxz.cnf", "w") as f2:
            p = subprocess.Popen("unxz", stdout=f2, stdin=f)
            p.wait()
    return "OK"


def presort_clauses(mode="global", seed="", shuffle=True, sbva=False):
    path = f"../data/presort{'_sbva' if sbva else ''}.cnf"
    try:
        with open(path, "w") as f2:
            p = subprocess.Popen(
                (
                    "python3",
                    "presort_clauses.py",
                    f"../data/{'sbva' if sbva else 'unxz'}.cnf",
                    seed,
                    mode,
                    "shuffle" if shuffle else "noshuffle",
                ),
                stdout=f2,
            )
            p.wait()
        return "OK"
    except FileNotFoundError:
        os.remove(path)
        return "NotFound"


loop = asyncio.get_event_loop()


def check_antisat(problem, program):
    try:
        stdout = loop.run_until_complete(check_stdin_unpacked(problem, program))
    except Exception as e:
        return e.__class__.__name__
    if isinstance(stdout, Exception):
        return str(stdout)
    stdout_last = stdout.split(b"\n")[-2]
    if stdout_last == b"SAT":
        return "SAT"
    if stdout_last == b"UNSAT":
        return "UNSAT"
    return "UNEXPECTED"


def antisat(i, inp, build_suffix, name_suffix):
    return (
        f"antisat{name_suffix}{i}",
        lambda _: check_antisat(f"../data/{inp}.cnf", f"./buildsat{build_suffix}{i}/triesat")
    )


def check_minisat(problem, program):
    try:
        stdout = loop.run_until_complete(check_stdin_unpacked(problem, program))
    except Exception as e:
        return e.__class__.__name__
    if isinstance(stdout, Exception):
        return str(stdout)
    stdout_last = stdout.split(b"\n")[-2]
    if stdout_last == b"SATISFIABLE":
        return "SAT"
    if stdout_last == b"UNSATISFIABLE":
        return "UNSAT"
    return "UNEXPECTED"


def minisat(version, inp):
    program = f"../MiniSat_v{version}/minisat"
    return f"minisat{version}_{inp}", lambda _: check_minisat(f"../data/{inp}.cnf", program)


def check_s(check):
    try:
        stdout = loop.run_until_complete(check)
    except Exception as e:
        traceback.print_exc()
        return e.__class__.__name__
    if isinstance(stdout, Exception):
        return str(stdout)
    stdout_lines = stdout.split(b"\n")
    if b"s SATISFIABLE" in stdout_lines:
        return "SAT"
    if b"s UNSATISFIABLE" in stdout_lines:
        return "UNSAT"
    return "UNEXPECTED"


def cadical(inp):
    program = f"../cadical/build/cadical"
    return f"cadical_{inp}", lambda _: check_s(check_stdin_unpacked(f"../data/{inp}.cnf", program))


def cryptominisat(inp):
    program = f"../cryptominisat/build/cryptominisat5"
    return f"cryptominisat_{inp}", lambda _: check_s(check_stdin_unpacked(f"../data/{inp}.cnf", program))


def sbva():
    p = subprocess.run(
        (
            "../SBVA/sbva",
            "-i",
            "../data/unxz.cnf",
            "-o",
            "../data/sbva.cnf",
            "-t",
            str(int(TIMEOUT)),
        ),
    )

    if p.returncode != 0:
        os.remove("../data/sbva.cnf")
        return "SbvaError"

    return "OK"


PROGRAMS = (
    ("unxz", unxz),
    ("presort", lambda _: presort_clauses(mode="global", seed="", shuffle=False)),
    ("sbva", lambda _: sbva()),
    ("presort_sbva", lambda _: presort_clauses(mode="global", seed="", shuffle=False, sbva=True)),
    *(antisat(i, "presort_sbva", "f", "_presort_fixedtrie_sbva") for i in range(12)),
    *(antisat(i, "sbva", "f", "_fixedtrie_sbva") for i in range(12)),
    *(antisat(i, "presort_sbva", "t", "_presort_trie_sbva") for i in range(12)),
    *(antisat(i, "sbva", "t", "_trie_sbva") for i in range(12)),
    *(antisat(i, "sbva", "", "_clause_sbva") for i in range(6)),
    minisat("1.12b", "sbva"),
    minisat("1.14", "sbva"),
    cadical("sbva"),
    cryptominisat("sbva"),
    *(antisat(i, "presort", "f", "_presort_fixedtrie") for i in range(12)),
    *(antisat(i, "unxz", "f", "_fixedtrie") for i in range(12)),
    *(antisat(i, "presort", "t", "_presort_trie") for i in range(12)),
    *(antisat(i, "unxz", "t", "_trie") for i in range(12)),
    *(antisat(i, "unxz", "", "_clause") for i in range(6)),
    minisat("1.12b", "unxz"),
    minisat("1.14", "unxz"),
    cadical("unxz"),
    cryptominisat("unxz"),
)

DRY_RUN = True
WRITE_MODE = "a"

if DRY_RUN:
    times_f = sys.stdout
    results_f = sys.stdout
else:
    times_f = open("times_sat.csv", WRITE_MODE)
    results_f = open("results_sat.csv", WRITE_MODE)


def measure_with(problem, program, quiet=False):
    print(f"{problem}\t{program[0]}", end="\t", flush=True)
    tic = time.time()
    result = program[1](problem)
    if not quiet:
        print(result, end=" ", file=results_f, flush=True)
    toc = time.time()
    print(f"{result}\t{toc - tic:.2f}", flush=True)
    if not quiet:
        print(f"{toc - tic:.2f}", end=" ", file=times_f, flush=True)


random.seed("qveo3tj309rfkv240")
for i, problem in enumerate(random.sample(PROBLEMS, 100)): # if i <= 25:
    # if i < 18:
    #     continue

    if i != 49:
        continue

    if i == 49:
        print(problem)
        for j, program in enumerate(PROGRAMS):
            if j == 7:
                print(program)
            if j == 60:
                print(program)

    for j, program in enumerate(PROGRAMS):
        if j < 4:
            measure_with(problem, program, quiet=True)
        elif j in (7, 60):
            measure_with(problem, program, quiet=True)


    # for j, program in enumerate(PROGRAMS):
    #     if i > 18 or j >= 103:
    #         measure_with(problem, program)
    #     elif j < 4:
    #         measure_with(problem, program, quiet=True)

    # print(file=results_f, flush=True)
    # print(file=times_f, flush=True)
